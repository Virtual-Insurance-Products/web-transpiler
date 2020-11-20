
(asdf:defsystem :web-transpiler
  :description "Experimental lisp->lisp transpiler for the web"
  :author "VIP"
  :serial t
  :depends-on ("macroexpand-dammit" "anaphors" "fare-matcher" "web-monad")
  
  :components ((:file "web-transpiler")
               
               )
  )
