
(in-package :cl-user)

(defpackage :web-transpiler
  (:use :cl :anaphors :web-monad :monads :web-utils)
  (:import-from :fare-matcher :match :ematch)
  (:export #:transpile #:web #:*first-half*))

(in-package :web-transpiler)


;; This is a funky lisp->lisp transpiler which transpiles CL into different CL
;; The target is much more like a VM code
;; The *reason* for doing this is to allow arbitrary linear page flow in web monad stuff
;; It will make it much easier to do things like wizardy things, whose logic tends to get a bit
;; tortured

;; With this we just generate a state machine from 'normal' CL. Actually a subset thereof unless
;; I find a better front end

;; The *output* of this is normal executable CL

;; NOTE: it might be a good idea, for safety, to serialize the VM state as JSON
;; I could also implement the ability to put any object with an accept/present-to-string implementation on the
;; stack too
;; I would need to know its class when doing that. TBC...


;; (ql:quickload :macroexpand-dammit)

(defun cl-compile (expression)
  ;; step 1: macro expand it all. Hurrah
  (let ((expression (macroexpand-dammit:macroexpand-dammit expression))
        (ops nil)
        (next-label 0)
        (tagbody-nest 0))
    (flet ((emit (op)
             (push op ops)))
      (labels ((comp (expression environment)
                 (flet ((find-var (name)
                          (labels ((find-in-frame (name frame &optional (n 0))
                                     (when frame
                                       (if (eq name (first frame))
                                           n
                                           (find-in-frame name (cdr frame) (+ n 1)))))
                                   (find-in-frames (name frames &optional (frame 0))
                                     (if frames
                                         (aif (find-in-frame name (first frames))
                                              (list it frame)
                                              (find-in-frames name (cdr frames) (+ frame 1)))
                                         (error "Undeclared free variable: ~A" name))))
                            (awhen (find-in-frames name environment)
                              `(lvar ,(first it) ,(second it))
                              #+nil`(nth ,(first it)
                                         (nth ,(second it) env))))))
                   (cond ((not expression)
                          (emit `(stack-push nil)))
                         ((atom expression)
                          (cond ((and (symbolp expression)
                                      (not (keywordp expression)))
                                 ;; emit variable reference
                                 ;; (note: we can only reference variables declared in here, not external
                                 ;; things. This is by design)
                                 (emit `(stack-push ,(find-var expression))))
                                (t (emit `(stack-push ,expression)))))

                       
                       
                         ;; default case is to just do a function call...
                         ((listp expression)
                          (match expression
                            ;; !!! PROGN
                            (`(progn . ,body)
                              (loop for (obj . rest) on (or body (list nil))
                                 do (comp obj environment)
                                 ;; drop the result otherwise we end up with things left on the stack
                                 when rest do (emit '(stack-pop))))

                            ;; !!! IF
                            (`(if ,test ,true . ,false)
                              (let ((false-part (incf next-label))
                                    (end-part (incf next-label))
                                    (false (cons 'progn false)))
                                (comp test environment)
                                (emit `(unless (stack-pop)
                                         (go ,false-part)))
                                (comp true environment)
                                (emit `(go ,end-part))
                                (emit false-part)
                                (comp false environment)
                                (emit end-part)))


                            ;; I could compile this in terms of lambdas
                            (`(let ,bindings . ,body)
                              (setf bindings
                                    (mapcar (lambda (b)
                                              (if (consp b)
                                                  b
                                                  (list b nil)))
                                            bindings))

                              (emit `(extend-env ,(length bindings)))
                              
                              ;; now we can compile the body with an extended environment
                              (comp `(progn
                                       ;; initialise the values
                                       ,@(mapcar (lambda (x)
                                                   `(setq ,@x))
                                                 bindings)
                                       ,@body)
                                    (cons (reverse (mapcar 'first bindings))
                                          environment))

                              ;; then pop the stack
                              (emit `(pop env)))
                          
                            (`(setq ,var ,value)
                              (comp value environment)
                              ;; !!! NOTE: don't side effect inside stack-push
                              ;; (generally keeping the ops small is good since it will make it
                              ;;  easier to optimize, if I ever bother to do that)
                              (emit `(set-lvar ,@ (cdr (find-var var))
                                                  (stack-pop))
                                    ;; `(setf ,(find-var var) (stack-pop))
                                    )
                              (emit `(stack-push ,(find-var var))))

                            (`(block ,name . ,body)
                              ;; now, if the name is not nil we will need to provide an exit from the block
                              ;; I'm not really sure how to do that. Do I need to unwind/save the stack?
                              ;; maybe.
                              (if (not name)
                                  (comp `(progn ,@body) environment)
                                  (error "Don't know how to compile named blocks yet!")))

                            (`(tagbody . ,body)
                              (incf tagbody-nest)
                              (loop for (thing . rest) on body
                                   do (if (atom thing)
                                          (emit (intern (format nil "~A~A" thing tagbody-nest)))
                                          (progn
                                            (comp thing environment)
                                            (when rest
                                              (emit '(stack-pop))))))
                              (decf tagbody-nest)
                              ;; !!! Shouldn't we return the value of the last form?
                              (emit '(stack-push nil)))
                            
                            (`(go ,label)
                              (emit `(go ,(intern (format nil "~A~A" label tagbody-nest)))))

                            (`(web ,object)
                              (let ((start (incf next-label)))
                                (emit `(setf *first-half* t))
                                (comp object environment)
                                ;; this essentially suspends operation of the VM
                                (emit `(return-from vm
                                         (show-web-monad ,start)))
                                (emit start)
                                (emit `(setf *first-half* nil))
                                ;; when we start up here the stack will be restored but
                                ;; show-web-monad pops the *monad* off the stack since
                                ;; we have no way to send the monad to the browser
                                ;; SO the call to get the monad to show must be output again
                                (comp object environment)
                                (emit `(get-web-monad-result))))
                          
                            ;; ignore
                            (`(declare . ,r) (emit '(stack-push nil)))

                            (`(quote ,x)
                              (cond ((or (stringp x)
                                         (numberp x))
                                     (comp x environment))
                                    (t (emit `(stack-push ,expression)))))
                            
                            ;; !!! GENERAL FUNCTION CALLS (FFI)
                            (* (dolist (arg (cdr expression))
                                 (comp arg environment))
                               (emit `(call ',(first expression) ,(length (cdr expression)))))))))))
        
        
        
        (comp expression nil))
      (reverse ops))))



;; beginnings of a peephole optimizer
(defun peephole-optimize (ops)
  (when ops
    (ematch ops
            (`((stack-push ,x)
               (stack-pop)
               . ,rest)
              ;; some things are not safe to do here - if the pushed thing is a general function call
              (if (or (atom x)
                      (and (consp x)
                           (eq (first x) 'lvar)))
                  (peephole-optimize rest)
                  `((stack-push ,x)
                    (stack-pop)
                    ,@(peephole-optimize rest))))

            
            (`((go ,a)
               (go ,b)
               . ,rest)
              (peephole-optimize `((go ,a)
                                   ,@rest)))
            
            (`((stack-push ,x)
               (set-lvar ,a ,b (stack-pop))
               . ,rest)
              (peephole-optimize `((set-lvar ,a ,b ,x)
                                   ,@rest)))

            ;; !!! The problem with these two is that the above will strip
            ;; out the call if followed immediately by a pop, which won't be correct if the called function had other side effects
            ;; we might like it not to, but we can't guarantee it won't
            ;; That's why I'm going to 'mask' the stack push to avoid the above optimization
            (`((stack-push ,a)
               (call ',op 1)
               . ,rest)
              (peephole-optimize `((stack-push (,op ,a))
                                   ,@rest)))
            
            ;; !!! Is this always valid to do? What if the function has side effects?
            (`((stack-push ,a)
               (stack-push ,b)
               (call ',op 2)
               . ,rest)
              (peephole-optimize `((stack-push (,op ,a ,b))
                                   ,@rest)))

            (* (cons (first ops)
                     (peephole-optimize (cdr ops)))))))

(defun repeated-peephole (ops)
  (let ((x (peephole-optimize ops)))
    (if (equal x ops)
        ;; if it doesn't change anything then we're done
        x
        ;; otherwise try again
        (repeated-peephole x))))

(defparameter *first-half* nil)

;; this will need to output a jump table too
(defun cl-wrap (expression &key (vm-prefix "_vm"))
  (let* ((ops (cl-compile expression))
         (jump-table
          ;; let's make the entry point jump table...
          (loop for op in ops
             for jump = (match op
                          (`(return-from vm (show-web-monad ,n)) n))
             when jump collect `(when (eql entry ,jump)
                                  (go ,jump)))))

    
    `(let ((*first-half* nil))
       (with-web-monad
         stack <- (mquery (format nil "~A_stack" ,vm-prefix))
         (setf stack (when stack (read-from-string stack)))

         entry <- (mquery (format nil "~A_continue" ,vm-prefix))
         (setf entry (when entry (parse-integer entry)))
       
         env <- (mquery (format nil "~A_env" ,vm-prefix))
         (setf env (when env (read-from-string env)))
       
         request <- (mrequest)
       
         (macrolet ((lvar (index frame)
                      `(nth ,index (nth ,frame env)))

                    (set-lvar (index frame value)
                      `(setf (nth ,index (nth ,frame env))
                             ,value))

                    (extend-env (n)
                      `(push (loop for i from 1 to ,n collect nil)
                             env)))
           (flet ((stack-push (x)
                    (push x stack))
                  (stack-pop ()
                    (unless stack (error "Stack underflow!"))
                    (pop stack))

                
              
                  ;; this is obviously going to incur considerable overhead, but I suspect I won't care
                  ;; It would definitely be good if I could eliminate some stack thrash
                  ;; I guess it's probably fairly easy to do that.
                  (call (f arg-count)
                    (push (apply f (reverse (loop for i from 1 to arg-count
                                               collect (pop stack))))
                          stack))

                  ;; now for the cunning part...
                  (show-web-monad (continue)
                    (let ((monad (pop stack)))
                      ;; this is achieved simply by wrapping it with some more code for saving the VM
                      ;; state
                      ;; all we need to know is where to branch to on wakeup, the stack &c
                      (with-web-monad
                        - (draw-context (format nil "~A_state" ,vm-prefix)
                                        (mhtml (:input :name (:print (format nil "~A_continue" ,vm-prefix))
                                                       :value continue
                                                       :type "hidden")
                                               ;; !!! This is kind of dangerous
                                               (:input :name (:print (format nil "~A_stack" ,vm-prefix))
                                                       :value (:format "~S" stack)
                                                       :type "hidden")

                                               (:input :name (:print (format nil "~A_env" ,vm-prefix))
                                                       :value (:format "~S" env)
                                                       :type "hidden"))
                                        ;; ALWAYS update the browser's copy of VM state after requests
                                        :redraw t)
                        (progn monad))))

                  ;; This could (perhaps) be done above rather than here
                  (get-web-monad-result ()
                    (push (web-monad-run (dont-render (pop stack))
                                         request)
                          stack)))
       
             (block vm
               (tagbody
                  ,@jump-table
                  ,@ (repeated-peephole ops))
           
               (if (cdr stack)
                   (error "Stack contains ~S" stack)
                   (unit (first stack))))))))))


;; now a macro for it...
;; name has a default. To use >1 of these transpiled program they must have unique names
;; so that their state doesn't conflict
;; It might be worth passing in an initial environment too I guess, although how could that be resovled?
(defmacro transpile ((&key (name "_vm_") naked (optimize #'repeated-peephole)) &body forms)
  (if naked
      `(tagbody
          ,@(funcall (or optimize (lambda (x) x))
                     (cl-compile `(progn ,@forms))))
      `(let ((vm-prefix (query-parameter-name ,name)))
         ,(cl-wrap `(progn ,@forms) :vm-prefix 'vm-prefix))))


;; NOTE: the representation of the environment could be a lot simpler. We could just use a linear array. Extending the environment would just increase a 'top' by N, destending it would decrease the top by N
;; getting and setting variables would just do a linear index into the environment by multiplying their two parameters.
;; that way we wouldn't need to keep allocating memory. 

;; actually that wouldn't quite work. We would need to know how many entries were in each frame. I'm sure that could be worked out at compile time though.




;; PHASE 2
;; =======

;; CL->JS compiler. How can I start to make progress with this?
;; What do I need to do to figure out what parts of the stack would need to be sent from the web client to the server so as to avoid unnecessary (and impossible) transfers?
;; do I need to explicitly delimit the 


;; I had envisaged some instructions like this:-

#+nil
(tagbody
   (go copy-environment)
 switch-to-server
   (rcall-or-something)

 copy-environment
   ;; now having compiled the body which will execute on the server we know what variables it required and can thus send them all here
   ;; ...
   (go switch-to-server)
   )

;; so, we compile the body of code which is going to execute on the server and keep track of what variables were access
;; it wouldn't matter if that code calls other things, since those other things wouldn't have access to the lexical environment
;; when we start to compile the code to execute on the server we can just generate a tag for the environment transmission and then after compiling it we generate that bit of code
;; Does this mean we have to delimit (in effect) the whole chunk which is to run on the server? I initially thought it would be nice to not require that, but we seem to need to know exactly what has to be sent to the server
;; we could just send everything, but that seems wasteful and like it wouldn't work in some cases.

;; Dynamic variables would cause a problem with this. It *might* be acceptable to just say that those won't transfer.
;; That might be a big problem with some patterns though.
;; Do we end up with no improvement of doing some kind of RPC API though? I don't think so. I think if we can (even) just send a lexical closure over to the server to run then we're probably quids in.
;; Anything else we want can probably be layered on top of that anyway. We can always just CPS transform the CL code, in which case we get those kind of delimited transfers anyway.

;; the LLVM relooper is interesting (see paper.pdf). It makes me wonder if it would be much more efficient to translate the CL code into more 'normal' looking JS, rather than JS which looks like assembly BUT this will inevitably limit us, AND it restricts our ability to do the sort of things the above can do with web monads. Maybe I just shouldn't worry about that. I *could* always do something like relooping.

