(in-package "ACL2")
(include-book "centaur/esim/defmodules" :dir :system)

(set-gc-strategy :delay)

:q

(save-exec "test-image"
           "Defmodules preloaded"
           :host-lisp-args "-Z 256M"
           :init-forms '((set-gc-strategy :delay)))
