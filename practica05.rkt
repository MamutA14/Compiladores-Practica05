#lang nanopass
(require nanopass/base)
(define-language L8
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (type (t)))
   (Expr (e body)
         x
         pr
         c    
         t  
         (quot c)
         (begin e* ... e)
         (primapp pr e* ...)
         (if e0 e1 e2 )
         (lambda ([x* t*] ...) body* ... body)
         (let ([x t e]) body* ... body)
         (letrec ([x t e] body* ... body))
         (letfun ([x t e] body* ... body))
         (list e* ...)
         (e0 e1 ...)))

(define (variable? x)
   (and (symbol? x) (not (memq x '(+ - * / and or)))))

(define (primitive? x)
  (or (procedure? x) (memq x '(and or + * / - car cdr))))


(define (constant? x)
  (or (number? x) (boolean? x)))

(define (type? t)
 (or (equal? t 'Int) (equal? t 'Bool) (eq? t 'String) (eq? t 'Char) (eq? t 'Lambda))) ;; T ::= Int | Bool | String | Char

(define-parser parse-L8 L8)

#|Ejercicio 1|#
(define-language L9
  (extends L8)
  (Expr (e body)
        (-
         (lambda ([x* t* ] ...) body* ... body)
         (e0 e1 ...)
         )
        (+
         (lambda ([x t ]) body* ... body)
         (e0 e1))
  )
)
(define-parser parse-L9 L9)

#|El proceso de currficación consite en
convertir una función de varios parametros
en una función de un solo:
add(x)-> \y=> x+y.
 La idea es curryficar lambda tal que
sus parametros adicionales se encuentren dentro  de otro lambda del body original  |#

(define-pass curry : L8(ir) -> L9()
  (Expr : Expr(ir) -> Expr()
        [(lambda ([,x*,t*]...),[body*] ... ,[body])
         ;;Definimos f como el conjunto de valores de x* t* 
         (let f ([paramsx* x*]
                 [paramst* t*])
           (if (equal? (length paramsx*) 1)
               `(lambda ([,(car paramsx*),(car paramst*)]) ,body* ...,body)
               `(lambda ([,(car paramsx*),(car paramst*)]),(f (cdr paramsx*) (cdr paramst*)))
               ))]
        [(,[e0],[e1]  ...)
         (let f ([paramse0 e0]
                 [paramse1 e1])
           (if (equal? (length paramse1 ) 0) 
               `,paramse0
               (f `(, paramse0 ,(car paramse1)) (cdr paramse1))
               ))]))


#|Ejercicio 2 |#
(define-language L10
  (extends L9)
  (Expr (e body)
        (-
         (quot c)
         )
        (+
         (const t c)
         )
  )
)
(define-parser parse-L10 L10)


(define-pass type-const : L9(ir) -> L10()
  (Expr : Expr(ir) -> Expr()
        [(quot , c) ;;(begin ,[e*] ... ,[e])
         (if (number? c )
       `(const , 'Int , c)
       `(const, 'Bool ,c))
        ])
   )