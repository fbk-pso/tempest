(define (domain mapanalyzer)
(:requirements :typing :durative-actions)
  (:types  
	car
	junction	
	garage
	road
	)

  (:predicates
    (connected ?x - junction ?y - junction ) ;; junctions in diagonal (on the map)
    (at_jun ?c - car ?x - junction) ;; a car is at the junction
    (starting ?c - car ?x - garage) ;; a car is in its initial position
    (arrived ?c - car ?x - junction) ;; a car arrived at destination
    (road_connect ?r1 - road ?xy - junction ?xy2 - junction) ;; there is a road that connects 2 junctions
    (clear ?xy - junction ) ;; the junction is clear, no vehicles
    (in_place ?x - road);; the road has been put in place
    (available ?x - road);; the road has been put in place
    (at_garage ?g - garage ?xy - junction ) ;; position of the starting garage

  )
(:functions 
	(distance ?initial - junction ?final - junction) 
	(build-time)
	(remove-time)
	(speed ?v - car)
	(arrived-time)
	(start-time)
	(total-cost)
)

;; move the vehicle: no limit on the number of vehicles on the road, but the junction must be clear at the end
(:durative-action move_vehicle_road
  :parameters (?xy_initial - junction ?xy_final - junction ?machine - car ?r1 - road)
  :duration (= ?duration (/ (distance ?xy_initial ?xy_final) (speed ?machine)))
  :condition (and 
		(at start (at_jun ?machine ?xy_initial))
		(at start (road_connect ?r1 ?xy_initial ?xy_final))
		(at start (in_place ?r1))
		(at end (clear ?xy_final))
		)
  :effect (and  
		(at start (clear ?xy_initial))
		(at end (at_jun ?machine ?xy_final))
		(at start (not (at_jun ?machine ?xy_initial)))
		(at end (increase (total-cost) (/ (distance ?xy_initial ?xy_final) (speed ?machine))))
		)
)


;; vehicle at the final position. They are removed from the network and position is cleared.
(:durative-action vehicle_arrived
  :parameters (?xy_final - junction ?machine - car )
  :duration (= ?duration (arrived-time))
  :condition (and 
		(at start (at_jun ?machine ?xy_final))
		)
  :effect (and  
		(at end (clear ?xy_final))
		(at end (arrived ?machine ?xy_final))
		(at end (not (at_jun ?machine ?xy_final)))
		(at end (increase (total-cost) (arrived-time)))
		)
)

;; vehicle moved from the initial garage in the network.
(:durative-action vehicle_start
  :parameters (?xy_final - junction ?machine - car ?g - garage)
  :duration (= ?duration (start-time)) 
  :condition (and 
		(at start (at_garage ?g ?xy_final))
		(at start (starting ?machine ?g))
		(at start (clear ?xy_final))
		)
  :effect (and  
		(at end (not (clear ?xy_final)))
		(at end (at_jun ?machine ?xy_final))
		(at start (not (starting ?machine ?g)))
		(at end (increase (total-cost) (start-time)))
		)
)

;; build road
(:durative-action build_road
  :parameters (?xy_initial - junction ?xy_final - junction ?r1 - road)
  :duration (= ?duration (* (distance ?xy_initial ?xy_final) (build-time))) 
  :condition (and 
		(at start (clear ?xy_final))
		(at start (available ?r1))
		(at start (connected ?xy_initial ?xy_final))
		)
  :effect (and  
		(at end (road_connect ?r1 ?xy_initial ?xy_final))
		(at end (road_connect ?r1 ?xy_final ?xy_initial))
		(at start (in_place ?r1))
		(at start (not (available ?r1)))
		(at end (increase (total-cost) (* (distance ?xy_initial ?xy_final) (build-time))))
		)
)

;; remove a road
(:durative-action remove_road
  :parameters (?xy_initial - junction ?xy_final - junction ?r1 - road)
  :duration (= ?duration (* (distance ?xy_initial ?xy_final) (remove-time))) 
  :condition (and 
		(at start (road_connect ?r1 ?xy_initial ?xy_final))
		(at start (road_connect ?r1 ?xy_final ?xy_initial))
		(at start (in_place ?r1))
		)
  :effect (and  
		(at end (not (in_place ?r1)))
		(at end (available ?r1))
		(at start (not (road_connect ?r1 ?xy_initial ?xy_final)))
		(at start (not (road_connect ?r1 ?xy_final ?xy_initial)))
		(at end (increase (total-cost) (* (distance ?xy_initial ?xy_final) (remove-time))))
		)
)




)
