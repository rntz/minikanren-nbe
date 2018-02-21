#lang racket

;; A minikanren implementation of intensional normalisation by evaluation for
;; the untyped lambda calculus (viewed as a fragment of Scheme).
;;
;; Based on http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
;;
;; I don't think this is possible. It might be possible with nominal logic, but
;; I don't think I'd really gain anything; NBE only works because it reuses the
;; host language's functions, and minikanren doesn't *really* have first-class
;; functions.
;;
;; Can I apply NBE *to* μkanren? Does μkanren have normal forms?

(require "miniKanren-with-symbolic-constraints/mk.rkt" "macros.rkt" "lists.rkt")

;; atomic values.
(define (atomo v) (conde [(symbolo v)] [(numbero v)]))
(define (¬closureo v)
  (conde [(atomo v)]
         [(fresh (x y) (== v (cons x y)) (=/= x 'closure))]))

(define (appo result-v func-v arg-v)
  (conde
   [(fresh (M)
      (¬closureo func-v)
      (reifyo M arg-v)
      (== result-v `(,func-v ,M)))]
   [(fresh (env x body)
      (== func-v `(closure ,env ,x ,body))
      (evalo result-v body `((,x . ,arg-v) . ,env)))]))

(define (evalo v term [env '()])
  (conde
   [(symbolo term)
    (conde [(assoco term v env)]
           [(¬assoco term env) (== v term)])]
   [(fresh (M N Mv Nv)
      (== term `(,M ,N))
      (evalo Mv M env)
      (evalo Nv N env)
      (appo v Mv Nv))]
   [(fresh (x body)
      (== term `(lambda (,x) ,body))
      (symbolo x)
      (=/= x 'lambda)
      (== v `(closure ,env ,x ,body)))]))

(define (reifyo M v)
  (conde
   [(¬closureo v) (== M v)]
   [(fresh (x env body y result the-body)
      (== v `(closure ,env ,x ,body))
      (== M `(lambda (,y) ,the-body))
      (symbolo y)
      ;; is (absento y v) sufficient to ensure freshness?
      ;; uh-oh, see 'should-fail, below.
      (absento y v)
      (evalo result body `((,x . ,y) . ,env))
      (reifyo the-body result))]))

(define (normo M term)
  (fresh (v)
   (evalo v term)
   (reifyo M v)))

;; WHAT THE HELL?
;; why does this succeed?
(define (should-fail)
 (run 1 (x)
   (absento x '(a b c))
   (== x 'a)))

(define (bad-query)
  (printf "running (normo `(lambda (x) x) M)\n")
  (run 3 (M) (normo `(lambda (x) x) M)))

(displayln "  reloaded!")
