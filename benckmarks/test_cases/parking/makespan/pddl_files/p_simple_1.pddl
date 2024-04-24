(define   (problem parking)
  (:domain parking)
  (:objects
     car_00  car_01 - car
     curb_00 curb_01 curb_02 curb_03 - curb
  )
  (:init
    (at-curb-num car_00 curb_00)
    (at-curb-num car_01 curb_01)
    (curb-clear curb_02)
    (curb-clear curb_03)
    (car-clear car_00)
    (car-clear car_01)
  )
  (:goal
    (and
      (at-curb-num car_00 curb_02)
      (at-curb-num car_01 curb_03)
    )
  )
(:metric minimize (total-time))
)
; =========== INIT ===========
;  curb_00: car_07 car_00
;  curb_01: car_04 car_05
;  curb_02: car_08 car_03
;  curb_03: car_11 car_02
;  curb_04: car_01
;  curb_05: car_13
;  curb_06: car_09
;  curb_07: car_06
;  curb_08: car_12
;  curb_09: car_10
;  curb_10:
;  curb_11:
;  curb_12:
;  curb_13:
;  curb_14:
;  curb_15:
;  curb_16:
;  curb_17:
;  curb_18:
;  curb_19:
;  curb_20:
;  curb_21:
;  curb_22:
;  curb_23:
; ========== /INIT ===========

; =========== GOAL ===========
;  curb_00: car_00
;  curb_01: car_01
;  curb_02: car_02
;  curb_03: car_03
;  curb_04: car_04
;  curb_05: car_05
;  curb_06: car_06
;  curb_07: car_07
;  curb_08: car_08
;  curb_09: car_09
;  curb_10: car_10
;  curb_11: car_11
;  curb_12: car_12
;  curb_13: car_13
;  curb_14:
;  curb_15:
;  curb_16:
;  curb_17:
;  curb_18:
;  curb_19:
;  curb_20:
;  curb_21:
;  curb_22:
;  curb_23:
; =========== /GOAL ===========
