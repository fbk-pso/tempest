(define (domain matchcellar)
     (:requirements :typing :durative-actions) 
     (:types match fuse) 
     (:predicates  
          (handfree) 
          (unused ?match - match) 
          (mended ?fuse - fuse)
	  (light ?match - match))
     (:functions
          (total-cost)
     )

     (:durative-action LIGHT_MATCH
          :parameters (?match - match)
          :duration (= ?duration 5)
          :condition (and
	       (at start (unused ?match)))
          :effect (and 
		(at start (not (unused ?match)))
		(at start (light ?match))
		(at end (not (light ?match)))
          (at end (increase (total-cost) 5))))


     (:durative-action MEND_FUSE 
          :parameters (?fuse - fuse ?match - match) 
          :duration (= ?duration 2) 
          :condition (and  
               (at start (handfree))
	       (over all (light ?match)))
          :effect (and
               (at start (not (handfree)))
               (at end (mended ?fuse))
               (at end (handfree))
               (at end (increase (total-cost) 2))))
)

