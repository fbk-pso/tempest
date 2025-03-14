(define (problem instance)
 (:domain matchcellar)
 (:objects 
    match0 - match
    fuse0 - fuse
)
 (:init 
  (handfree)
  (unused match0)
  (= (total-cost) 0)
)
 (:goal
  (and
     (mended fuse0)
))
 (:metric minimize (total-cost))
)
