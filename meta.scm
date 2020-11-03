;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; FILE: meta.scm
;
; DESCRIPTION: Create a metacircular interpreter for popl as a small subset of
; Scheme. The interpreter provide a read-eval-print loop (REPL) supporting:
; define, lambda, let, let*, list, cons, car, cdr, set!, if, cond, eq?, equal?,
; quote, null?, =, *, -, +, /. The interpreter also relies on Scheme itself for
; any of the primitive data types and procedures. When errors occur, a message
; will be printed and control return to the top of the REPL.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; metacircular interpreter for a subset of scheme
(load-option 'format)

(define (popl-error string)
  ; Output a given error message and abort the program. This one just calls
  ; scheme's error function.
  (format #t "ERROR: ~A~%" string)
  (*LOOPTOP* #!unspecific))

(define (popl-bind symbol value env)
  ; Add a binding from symbol to value in the given environment.
  ; Shadows any previous binding of the same symbol, perhaps permanently.
  (let ((bindings (car env)))
    (set-car! env (cons (list symbol value) bindings)))
  symbol)

(define (popl-get-binding symbol env)
  ; Look up the binding for a symbol in the environment.
  ; Used internally by env-value and popl-eval-set!
  (assoc symbol (car env)))

(define (env-value symbol env)
  ; Return the value of a symbol bound in the given environment.
  ; Error if the symbol is not bound.
  ; If symbol is bound, pr is true. Else pr is false.
  (let ((pr (popl-get-binding symbol env)))
    (if pr
        ;; If symbol is bound, return value bounded to symbol.
        (cadr pr)
        ;; If symbol is not bound, error message is sent.
        (popl-error (format #f "Undefined variable: ~A" symbol)))))

(define (popl-eval-define symbol value env)
  ; Implementation of define special form. Adds new binding to environment
  ; and returns the symbol that was defined.
  (popl-bind symbol value env)
  symbol)

(define (popl-eval-set! symbol value env)
  ; Find existing binding for symbol, and change its value to something new.
  ; Throws error if given symbol is not bound." Return original value associated
  ; with the modified symbol.
  (let* ((pr (popl-get-binding symbol env))
         (prev-val (cadr pr)))
    (if pr
        (set-car! (cdr pr) (popl-eval value env))
        (popl-error (format #f " Unbounded variable: ~A" symbol)))
    prev-val))

; An environment is a list of one element. That element is an association list.
; This allows us to add a binding to an environment.
(define *TOP-ENVIRONMENT* (list (list)))

; will be set! later to the continuation at the top of the popl-repl loop
(define *LOOPTOP* #!unspecific)

;; Predefined primitive functions.
(popl-eval-define '+ + *TOP-ENVIRONMENT*)
(popl-eval-define '- - *TOP-ENVIRONMENT*)
(popl-eval-define '* * *TOP-ENVIRONMENT*)
(popl-eval-define '/ / *TOP-ENVIRONMENT*)
(popl-eval-define '= = *TOP-ENVIRONMENT*)
(popl-eval-define '< < *TOP-ENVIRONMENT*)
(popl-eval-define '> > *TOP-ENVIRONMENT*)
(popl-eval-define 'car car *TOP-ENVIRONMENT*)
(popl-eval-define 'cdr cdr *TOP-ENVIRONMENT*)
(popl-eval-define 'eq? eq? *TOP-ENVIRONMENT*)
(popl-eval-define 'equal? equal? *TOP-ENVIRONMENT*)
(popl-eval-define 'null? null? *TOP-ENVIRONMENT*)
(popl-eval-define 'cons cons *TOP-ENVIRONMENT*)
(popl-eval-define 'format format *TOP-ENVIRONMENT*)

(define (popl-apply function arguments)
  ; Implementation of function-calling lambdas.
  ; Extracts the pieces of the lambda and copies the environment,
  ; binds each parameter, recursively evaluates each form in the body in
  ; the copied environment. Todo: needs to check to make sure number of
  ; arguments matches number of parameters and throw an error if not.
  (let* ((lambda-parameters (first function))
         (lambda-body (second function))
         (lambda-env (third function))
         (env (list (first lambda-env))))
    (for-each (lambda (pair) (popl-bind (car pair) (cadr pair) env))
       (zip lambda-parameters arguments))
    (let ((result #!unspecific))
      (for-each (lambda (form) (set! result (popl-eval form env)))
          lambda-body)
      result)))

(define (popl-eval-let bindings forms env)
  ; for each pair in binding, call popl-bind to add it to the new environment.
  ; Then evaluate each form in forms using the new environment
  (let ((new-env (list (car env))))
    ; evaluate symbol in the old environment,
    ; but add the evaluated value to the new environment
    (for-each (lambda (binding) (popl-bind (car binding)
                                           (popl-eval (cadr binding) env)
                                           new-env))
       bindings)
    (let ((result #!unspecific))
    ; evaluate the forms in the new environment
     (for-each (lambda (form) (set! result (popl-eval form new-env)))
         forms)
     result)))

(define (popl-eval-let* bindings forms env)
  ; for each pair in binding, call popl-bind to add it to defined environment.
  ; Then evaluate each form in forms using the defined environment
  (let ((env (list (car env))))
  ; evaluate symbol in the old environment,
  ; but add the evaluated value to the old environment
    (for-each (lambda (binding) (popl-bind (car binding)
                                           (popl-eval (cadr binding) env)
                                           env))
      bindings)
    (let ((result #!unspecific))
      ; evaluate the form in the old environment
      (for-each (lambda (form) (set! result (popl-eval form env)))
          forms)
      result)))

(define (popl-eval-format expr env)
  ; determine whether if the output string has additional argument,
  ; use format to output the string and additional argument if exist.
  (if (not (null? (cdddr expr)))
    (format (second expr) (third expr) (popl-eval (fourth expr) env))
    (format (second expr) (third expr))))

(define (popl-eval-list expr env)
  ; create a procedure list using Scheme's procedure cons
  (if (null? expr)
    expr
    (cons (popl-eval (car expr) env) (popl-eval-list (cdr expr) env))))

(define (popl-eval-cond expr env)
  ; create a procedure cond using Scheme procedure if
  ;check if first cond has any (true) conditions
  (if (null? expr)
    #!unspecific
    ; check if the first condition is the only condition
    (if (null? (cdr expr))
      ; check if there is else statement if all condition run out
      (if (eq? (car (first expr)) 'else)
        (popl-eval (cadr (first expr)) env)
        ; if first condition is true
        (if (popl-eval (car (first expr)) env)
          ; check if first condition return anything
          ; if not, return true since the condition must already be true
          (if (null? (cdr (first expr)))
            #t
            ; if yes, return what first condition wanted
            (popl-eval (cadr (first expr)) env))
          #!unspecific))
      ; if first condition is true
      (if (popl-eval (car (first expr)) env)
        ; check if first condition return anything, if not, return true
        (if (null? (cdr (first expr)))
          #t
          ; if yes, return what first condition wanted
          (popl-eval (cadr (first expr)) env))
        ; go to the next condition
        (popl-eval-cond (cdr expr) env)))))

(define (popl-lambda-duplicated-parameters expr env)
  ; check if lambda's parameters have duplicate
  (if (null? expr)
    #f
    (if (member (first expr) (cdr expr))
      #t
      (popl-lambda-duplicated-parameters (cdr expr) env))))

(define (popl-eval expr env)
  ; This is the main evaluator. It is where you will add code to implement
  ; more features of popl. You may also add helper functions
  ;  in the spirit of popl-eval-define, popl-eval-set!, and popl-apply.
        ; numbers, booleans, null list all just evaluate to themselves
  (cond ((or (number? expr) (boolean? expr) (null? expr) (string? expr)) expr)
        ; If you have a symbol to evaluate, look it up!
        ((symbol? expr) (env-value expr env))
        ; pair could be a lot of things.  Check each special form...
        ((pair? expr)
               ; if define function called something in popl enviroment
         (cond ((eq? (first expr) 'define) ; (define sym value)
                (if (or (null? (cdr expr)) (null? (cddr expr)))
                  (popl-error (format #f "Ill-formed special form: ~S" expr))
                  (let ((sym (second expr))
                        (val (popl-eval (third expr) env)))
                    (popl-eval-define sym val env))))
               ; if  lambda function called in popl environment
               ((eq? (first expr) 'lambda) ; (lambda parameters body)
                (if (or (null? (cddr expr)) (popl-lambda-duplicated-parameters (second expr) env))
                  (popl-error (format #f "Ill-formed special form: ~S" expr))
                  (list (second expr) ; formal parameters
                        (cddr expr)   ; body
                        env)))        ; environment
               ; if  let function called in popl environment
               ((eq? (first expr) 'let)  ; (let BINDINGS FORM1 FORM2......)
                (popl-eval-let (second expr) (cddr expr) env))
               ; if  let* function called in popl environment
               ((eq? (first expr) 'let*)  ; (let BINDINGS FORM1 FORM2......)
                (popl-eval-let* (second expr) (cddr expr) env))
               ; ; if list function called in popl environment
               ((eq? (first expr) 'list) ; (list form1 form2 ...)
                (popl-eval-list (cdr expr) env))
               ; ; if  cons function called in popl environment
               ((eq? (first expr) 'cons) ; (cons 'form1 'form2)
                (cons (popl-eval (second expr) env) (popl-eval (third expr) env)))
                ; if  set! function called in popl environment
               ((eq? (first expr) 'set!) ; (set! form1 form2)
                (popl-eval-set! (second expr) (third expr) env))
               ; if  if function called in popl environment
               ((eq? (first expr) 'if)               ; (if condition
                (if (popl-eval (second expr) env)       ;return if true
                    (popl-eval (third expr) env)        ; else)
                    (popl-eval (fourth expr) env)))
               ; if  cond function called in popl environment
               ((eq? (first expr) 'cond)          ; (cond condition1
                (popl-eval-cond (cdr expr) env))        ; condition2...)
               ; if  quote function called in popl environment
               ((eq? (first expr) 'quote)
                (second expr))
                ; if null? function called in popl environment
               ((eq? (first expr) 'null?)
                (null? (popl-eval (second expr) env)))
                ; if formate function called in popl environment
               ((eq? (first expr) 'format)
                (popl-eval-format expr env))
                (else ; but if not a special form, must be a function call.
                  (let* ((items (map (lambda (form) (popl-eval form env)) expr))
                         (function (first items)))
                     (if (procedure? function) ;; if function is built in.
                       (apply function (cdr items))
                       ; if function is not built in, check if the function has
                       ; parameters and how many arguments it had received
                       (if (= (length (first function)) (length (cdr items)))
                          (popl-apply function (cdr items))
                          (popl-error (format #f "Function expected ~S arguments, but ~S given" (length (first function)) (length (cdr items))))))))))
        (else "I don't know")))

(define (popl-repl)
  ; To create and enter the popl environment
  ; a continuation loop so that user can stay in the environment
  ;for as long as possiblem
  (call-with-current-continuation (lambda (here) (set! *LOOPTOP* here)))
  (let loop ()
  (format #t "H]=> ") ; popl environment display
  (let ((expr (read)))
    ; call (exit) to exit popl environment
    (cond ((equal? expr '(exit)) (format #t "~A~%" "Exited Enviroment"))
          (else (format #t "~A~%" (popl-eval expr *TOP-ENVIRONMENT*))
                (loop))))))
