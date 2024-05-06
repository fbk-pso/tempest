


(define (problem turnandopen-2-8-12)
(:domain turnandopen-strips)
(:objects robot1 - robot
    rgripper1 lgripper1 - gripper
    room1 room2 - room
    door1 - door
    ball1 ball2 - myobject)
(:init
    (closed door1)
    (doorknob-turned door1 rgripper1)
    ;;(open door1)
    (connected room1 room2 door1)
    (connected room2 room1 door1)
    (loc-robby robot1 room1)
    (free robot1 rgripper1)
    (free robot1 lgripper1)
    (loc ball1 room1)
    (loc ball2 room1)
(= (total-cost) 0)
)
(:goal
    (and
        ;;(loc ball1 room2)
        ;;(loc ball2 room2)
        ;;(carry robot1 ball1 lgripper1)
        (loc-robby robot1 room2)
    )
)
(:metric minimize (total-cost))

)
