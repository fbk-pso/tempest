(define (domain driverlog)
  (:requirements :typing :durative-actions) 
  (:types location driver truck obj)

  (:predicates
        (at_driver ?driver - driver ?loc - location)
        (at_truck ?truck - truck ?loc - location)
        (at_obj ?obj - obj ?loc - location)
		(in ?obj1 - obj ?obj - truck)
		(driving ?d - driver ?v - truck)
		(link ?x ?y - location) (path ?x ?y - location)
		(empty ?v - truck)
)
(:functions (total-cost))

(:durative-action LOAD-TRUCK
  :parameters
   (?obj - obj
    ?truck - truck
    ?loc - location)
  :duration (= ?duration 2)
  :condition
   (and 
   (over all (at_truck ?truck ?loc)) (at start (at_obj ?obj ?loc)))
  :effect
   (and (at start (not (at_obj ?obj ?loc))) (at end (in ?obj ?truck))
        (at end (increase (total-cost) 2))))

(:durative-action UNLOAD-TRUCK
  :parameters
   (?obj - obj
    ?truck - truck
    ?loc - location)
  :duration (= ?duration 2)
  :condition
   (and
        (over all (at_truck ?truck ?loc)) (at start (in ?obj ?truck)))
  :effect
   (and (at start (not (in ?obj ?truck))) (at end (at_obj ?obj ?loc))
        (at end (increase (total-cost) 2))))

(:durative-action BOARD-TRUCK
  :parameters
   (?driver - driver
    ?truck - truck
    ?loc - location)
  :duration (= ?duration 1)
  :condition
   (and 
   (over all (at_truck ?truck ?loc)) (at start (at_driver ?driver ?loc)) 
	(at start (empty ?truck)))
  :effect
   (and (at start (not (at_driver ?driver ?loc))) 
	(at end (driving ?driver ?truck)) (at start (not (empty ?truck)))
  (at end (increase (total-cost) 1))))

(:durative-action DISEMBARK-TRUCK
  :parameters
   (?driver - driver
    ?truck - truck
    ?loc - location)
  :duration (= ?duration 1)
  :condition
   (and (over all (at_truck ?truck ?loc)) (at start (driving ?driver ?truck)))
  :effect
   (and (at start (not (driving ?driver ?truck))) 
	(at end (at_driver ?driver ?loc)) (at end (empty ?truck))
  (at end (increase (total-cost) 1))))

(:durative-action DRIVE-TRUCK
  :parameters
   (?truck - truck
    ?loc-from - location
    ?loc-to - location
    ?driver - driver)
  :duration (= ?duration 10)
  :condition
   (and (at start (at_truck ?truck ?loc-from))
   (over all (driving ?driver ?truck)) (at start (link ?loc-from ?loc-to)))
  :effect
   (and (at start (not (at_truck ?truck ?loc-from))) 
	(at end (at_truck ?truck ?loc-to))
  (at end (increase (total-cost) 10))))

(:durative-action WALK
  :parameters
   (?driver - driver
    ?loc-from - location
    ?loc-to - location)
  :duration (= ?duration 20)
  :condition
   (and (at start (at_driver ?driver ?loc-from)) 
	(at start (path ?loc-from ?loc-to)))
  :effect
   (and (at start (not (at_driver ?driver ?loc-from)))
	(at end (at_driver ?driver ?loc-to))
  (at end (increase (total-cost) 20))))
 
)
