(define (problem DLOG-2-2-2)
	(:domain driverlog)
	(:objects
	driver1 - driver
	truck1 - truck
	package1 - obj
	s0 - location
	s1 - location
	)
	(:init
	;;(at_driver driver1 s0)
	(at_truck truck1 s0)
	;;(empty truck1)
	(driving driver1 truck1)
	;;(at_obj package1 s0)
	(in package1 truck1)
	(path s0 s1)
	(path s1 s0)
	(link s0 s1)
	(link s1 s0)
  	(= (total-cost) 0)
)
	(:goal (and
	;;(at_obj package1 s1)
	(at_obj package1 s0)
	;;(at_truck truck1 s1)
	))

(:metric minimize (total-cost))

)
