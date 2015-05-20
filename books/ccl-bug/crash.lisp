(set-debugger-enable t)

(defconst *config*
  (vl2014::make-vl-loadconfig
   :start-files (list "../centaur/esim/tutorial/alu16.v")))

(defconsts (*loadresult* state)
  (vl2014::vl-load *config*))

(vl2014::vl-loadresult-p *loadresult*)

(defconsts (*good* *bad*)
  (vl2014::vl-simplify (vl2014::vl-loadresult->design *loadresult*)
                       vl2014::*vl-default-simpconfig*))
