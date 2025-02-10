(define (problem citycar-2-2-1)
(:domain mapanalyzer)
(:objects  
junction0-0 junction0-1 
junction1-0 junction1-1 - junction
car0 - car
garage0 - garage
road0 road1 road2 road3 - road
)
(:init
	(=(build-time) 5)
	(=(remove-time) 3)
	(=(arrived-time) 1)
	(=(start-time) 1)
	(=(speed car0) 7)
(available road0)
(available road1)
(available road2)
(available road3)
(connected junction0-0 junction0-1)
(connected junction0-1 junction0-0)
(=(distance junction0-0 junction0-1) 76)
(=(distance junction0-1 junction0-0) 76)
(connected junction1-0 junction1-1)
(connected junction1-1 junction1-0)
(=(distance junction1-0 junction1-1) 14)
(=(distance junction1-1 junction1-0) 14)
(connected junction0-0 junction1-0)
(connected junction1-0 junction0-0)
(=(distance junction0-0 junction1-0) 17)
(=(distance junction1-0 junction0-0) 17)
(connected junction0-1 junction1-1)
(connected junction1-1 junction0-1)
(=(distance junction0-1 junction1-1) 81)
(=(distance junction1-1 junction0-1) 81)
(clear junction0-0)
(clear junction0-1)
(clear junction1-0)
(clear junction1-1)
(at_garage garage0 junction0-0)
(starting car0 garage0)
)
(:goal
(and
(arrived car0 junction1-1)
)
)
(:metric minimize (total-time))
)
