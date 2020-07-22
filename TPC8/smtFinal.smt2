(set-logic QF_AUFLIA)

(declare-fun max () Int)

; Matriz durações
(declare-fun d0_0 () Int)
(declare-fun d1_0 () Int)
(declare-fun d2_0 () Int)
(declare-fun d0_1 () Int)
(declare-fun d1_1 () Int)
(declare-fun d2_1 () Int)

; Matriz start-time
(declare-fun t0_0 () Int)
(declare-fun t1_0 () Int)
(declare-fun t2_0 () Int)
(declare-fun t0_1 () Int)
(declare-fun t1_1 () Int)
(declare-fun t2_1 () Int)

; The start time of the first task of every job i must be greater than or equal to zero
(assert (>= t0_0 0))
(assert (>= t1_0 0))
(assert (>= t2_0 0))

; The end time of the last task must be less than or equal to max
(assert (<= (+ t0_1 d0_1) max))
(assert (<= (+ t1_1 d1_1) max))
(assert (<= (+ t2_1 d2_1) max))

; Precedence
(assert (< (+ t0_0 d0_0) t0_1))
(assert (< (+ t1_0 d1_0) t1_1))
(assert (< (+ t2_0 d2_0) t2_1))

; Resource
(assert (or (>= t0_0 (+ t1_0 d1_0)) (>= t1_0 (+ t0_0 d0_0))))
(assert (or (>= t0_1 (+ t1_1 d1_1)) (>= t1_1 (+ t0_1 d0_1))))
(assert (or (>= t0_0 (+ t2_0 d2_0)) (>= t2_0 (+ t0_0 d0_0))))
(assert (or (>= t0_1 (+ t2_1 d2_1)) (>= t2_1 (+ t0_1 d0_1))))
(assert (or (>= t1_0 (+ t0_0 d0_0)) (>= t0_0 (+ t1_0 d1_0))))
(assert (or (>= t1_1 (+ t0_1 d0_1)) (>= t0_1 (+ t1_1 d1_1))))
(assert (or (>= t1_0 (+ t2_0 d2_0)) (>= t2_0 (+ t1_0 d1_0))))
(assert (or (>= t1_1 (+ t2_1 d2_1)) (>= t2_1 (+ t1_1 d1_1))))
(assert (or (>= t2_0 (+ t0_0 d0_0)) (>= t0_0 (+ t2_0 d2_0))))
(assert (or (>= t2_1 (+ t0_1 d0_1)) (>= t0_1 (+ t2_1 d2_1))))
(assert (or (>= t2_0 (+ t1_0 d1_0)) (>= t1_0 (+ t2_0 d2_0))))
(assert (or (>= t2_1 (+ t1_1 d1_1)) (>= t1_1 (+ t2_1 d2_1))))

; Durações da tabela dos slides
(assert (= d0_0 2))
(assert (= d0_1 1))
(assert (= d1_0 3))
(assert (= d1_1 1))
(assert (= d2_0 2))
(assert (= d2_1 3))

; Respostas

; Podemos fazer todos os trabalhos com max = 10?
(push)
(assert (= max 10))
(check-sat)
(pop)

; Ainda e possıvel fazer todos os trabalhos em menos de 10 unidades de tempo?
(push)
(assert (< max 10))
(check-sat)
(pop)

; Ainda e possivel em 8 unidades de tempo?
(push)
(assert (= max 8))
(check-sat)
(pop)

; Ainda e possivel em menos de 8 unidades de tempo?
(push)
(assert (< max 8))
(check-sat)
(pop)
