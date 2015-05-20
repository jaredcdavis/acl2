(in-package "ACL2")
(include-book "centaur/esim/defmodules" :dir :system)

:q

(defun vl2014::vl-gc ()
  ;; Ensure that calls of vl-gc will always garbage collect.
  (gc$)
  nil)

(save-exec "test-image"
           "Defmodules preloaded"
           :host-lisp-args "-Z 256M"
           :init-forms '((set-gc-strategy :delay)))
