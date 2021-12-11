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
         (letrec ([x t e]) body* ... body)
         (letfun ([x t e]) body* ... body)
         (list e* ...)
         (e0 e1 ...)))

(define (variable? x)
   (and (symbol? x) (not (memq x '(+ - * / and or)))))

(define (primitive? x)
  (or (procedure? x) (memq x '(and or + * / - car cdr))))


(define (constant? x)
  (or (number? x) (boolean? x)))

(define (type? t)
 (or (equal? t 'Int) (equal? t 'Bool) (eq? t 'String) (eq? t 'Char) (eq? t 'Lambda) (eq? t 'List)
        (and (list? t) (equal? (car t) 'List) (equal? (cadr t) 'of) (type? (caddr t)) )
        (and (list? t) (type? (car t))  (equal? (cadr t) '-> ) (type? (caddr t)))  )) ;; T ::= Int | Bool | String | Char | List of T | T -> T

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


;; Ejercicio 3


;; PRIMERO DEFINIREMOS UNAS FUNCIONES AUXILIARES

;; Definimos la funcion unify
(define (unify t1 t2)
    (if (and (type? t1) (type? t2))
        (cond
            [(equal? t1 t2) #t]
            [(and (equal? 'List t1) (list? t2))  (equal? (car t2) 'List) ]
            [(and (equal? 'List t2) (list? t1))  (equal? (car t1) 'List) ]
            [(and (list? t1) (list? t2)) (and (unify (car t1) (car t2)))]
            [else #f])
        (error "Se esperaban 2 tipos")))

;; Unas funciones auxiliares para realizar la busqueda de variables en el ambiente
(define (find-type x env)
    (cond
        [(empty? env) (error "Error, variable no esta en el ambiente")]
        [(eq? (caar env) x) (cadar env)] ;; caso cuando el ambiente tiene la forma '( (x t) ... ) , devolvemos t
        [else (find-type x (cdr env))] ))  ;; llamada recursiva sobre el resto del ambiente si no coincide


;; Funcion que dada una variable x, un tipo t y un ambiente env devuelve un nuevo ambiente
;; resultado de agregar la tupla (x,t) al ambiente
(define (add-var-to-env x t env)
    (list (list x t) env))

;; Funcion que verifica que dada una lista de tipos args, estos tipos sean los correctos para la operacion pr
(define (check-args-types pr args )
    (case pr
        [(+ - * /) (andmap (lambda (x) (equal? x 'Int)) args) ]  ;; Estas primitivas son sobre enteros
        [(car cdr length) (andmap (lambda (x) (and (list? x) (equal? (car x) 'List))) args) ] ))  ;; Estas operaciones van sobre listas




;; AHORA IMPLEMENTAMOS LA FUNCION J
(define (J e env)
    (nanopass-case (L10 Expr) e
        [,x  (find-type x env)]         ;; para variables buscamos directamente en el ambiente

        [(const ,t ,c ) t]              ;; para constantes tenemos el tipo especificado en el const

        [(begin ,e* ... ,e) (J e env)]   ;; Retornamos el tipo de la ultima exprexion

        [(primapp ,pr ,e* ...)
            (if (check-args-types pr  (map (lambda (x) (J x env)) e*) )
                (case pr
                    [(+ - * / length) 'Int]
                    [(car) (caddr (car  (map (lambda (x) (J x env)) e*)))]
                    [(cdr) (car  (map (lambda (x) (J x env)) e*) )])
                (error 'J "Los tipos de ~a no son compatbles para la operacion ~a" e* pr))]

        ;; Para el if verificamos que el tipo de e0 sea Bool, y los tipos de e1 y e2 sean los mismos
        [(if ,e0 ,e1 ,e2)
            (if (and (equal?  (J e0 env) 'Bool)  (unify (J e1 env) (J e2 env)))
                (J e1 env)
                (error 'J "El tipo de ~a debe ser Bool. Y el tipo de ~a debe ser igual al de ~a " e0 e1 e2) )]

        ;; Para las lambdas el tipo es t -> type_of_body
        [(lambda ([,x ,t]) ,body)  (list t '->  (J body (add-var-to-env x t env)))]

        ;; para expresiones let devolvemos el tipo del body agregando (x t) al ambiente
        [(let ([,x ,t ,e]) ,body)
            (if  (unify t (J e env))
                (J body (add-var-to-env x t env))
                ;; hay un error si el tipo de e no coincide con t
                (error 'J "El tipo de ~a no coincide con el de la expresion ~a." x e) )]

        ;; para expresiones letrec devolvemos el tipo del body agregando (x t) al ambiente
        [(letrec ([,x ,t ,e]) ,body)
            (if  (unify t (J e (add-var-to-env x t env)))
                (J body (add-var-to-env x t env))
                ;; hay un error si el tipo de e no coincide con t
                (error 'J "El tipo de ~a no coincide con el de la expresion ~a." x e) )]

        ;; Para expresiones letrec devolvemos el tipo del body agregando (x t) al ambiente
        [(letfun ([,x ,t ,e]) ,body)
            (if  (and (equal? '-> (cadr t)) (unify t (J e env)) )
                (J body (add-var-to-env x t env))
                ;; hay un error si el tipo de e no coincide con t
                (error 'J "El tipo de ~a no coincide con el de la expresion ~a." x e) )]

        [(list ,e* ...)
            ;; si es la lista vacia devoldemos List
            (if (empty? e*)
                'List
                ;; Calculamos los tipos de los elementos
                (let* ([types (map (lambda (x) (J x env)) e*) ]
                        [t1 (car types)])
                    ;; Si todos los mismos son los mismos deovlvemos List of T1
                    (if (andmap (lambda (x) (unify x t1)) types)
                        (list 'List 'of t1)
                        (error 'J "Los elementos de la lista ~a no son del mismo tipo." e*)))  )]

        [(,e0 ,e1)
            (let ([t0 (J e0 env)] [t1 (J e1 env)])
                (if (and (list? t0) (equal? (cadr t0) '->) (unify (car t0) t1))  ;; verificamos que el tipo de e0 sea T1->T2 y el de e1 sea T1
                    (caddr t0)                                                   ;; Al aplicar la funcion se devuelve T2
                    (error 'J "El tipo de ~a no es compatible con el de ~a  para realizar la aplicacion de funcion." e0 e1) )  )]
  ))
