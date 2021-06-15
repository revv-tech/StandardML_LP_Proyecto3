use "sintax.sml";
use "vars.sml";
use "gen_bools.sml";
use "as_vals.sml";
use "evalProp.sml";
use "taut.sml";

(*PRUEBA 1*)
val p = variable "p"
val q = variable "q"
val hitotsu = (p :&&: p) :=>: (q :||: ~:q)

val prueba1 = implicacion( conjuncion(variable "p", variable "p") , disyuncion(variable "q", constante false))
val a = disyuncion(negacion(variable "p"), constante true);
(*Forma Normal Disyuntiva*)
fun fnd prop = 

    let
        val variables = vars prop
        
        val n = length variables
        
        val listaBooleanos = gen_bools n
        
        fun fndAux []                  = []

        |   fndAux (fila :: mas_filas) = 
                let

                    val asociacion = as_vals variables fila
                    
                    val evaluacion_es_verdadera = evalProp asociacion prop

                in
                    if evaluacion_es_verdadera then

                        [asociacion] @ fndAux mas_filas 
                    else

                        fndAux mas_filas 
                end
        fun toProp [] = []

            | toProp (lista :: mas_listas) = 

                let

                    fun first (x, _) = x
                    fun second (_, y) = y

                    fun toPropAux [] = []

                    | toPropAux( tupla :: mas_tuplas) = 

                        let
                            val nombre = first tupla
                            val valorBool =  second tupla
                        in
                            if valorBool then
                                [(variable nombre)] @ toPropAux mas_tuplas
                            else
                                [~:(variable nombre)] @ toPropAux mas_tuplas
                        end
                        
                in 
                    [toPropAux lista] @ toProp mas_listas
                end
        fun gc [] = constante true
            | gc ([prop]) = prop
            | gc (var :: mas_variables) =  
                (conjuncion (var ,gc(mas_variables)))
        
        fun gd [] = constante false
            | gd ([prop]) = prop
            | gd (var :: mas_variables) =  
                (disyuncion (var ,gd (mas_variables)))

        val tmp = fndAux listaBooleanos
        val tmp2 = toProp tmp
        val newGC = map gc
        val tmp3 = newGC tmp2
        val tmpFinal = gd tmp3
    
    in
    	tmpFinal
    end
;

(*IMPRESION BONITA*)
fun bonita prop =
	case prop of
        constante false             => "false"
    |   constante true              => "true"
    |   variable nombre             => "verbatim(" ^ nombre ^ ")"
    |   negacion prop1              => "~ (" ^ bonita  prop1 ^ ")"
    |   conjuncion (prop1, prop2)   => "(" ^ bonita prop1 ^ " /\\ " ^ bonita prop2 ^ ")"
    |   disyuncion (prop1, prop2)   => "(" ^ bonita prop1 ^ " \\/ " ^ bonita prop2 ^ ")"
    |   implicacion (prop1, prop2)  => "(" ^ bonita prop1 ^ " => " ^ bonita prop2 ^ ")"
    |   equivalencia (prop1, prop2) => "(" ^ bonita prop1 ^ " <=> " ^ bonita prop2 ^ ")"
;

(*SIMPLIFICACION*)
fun simpl prop =
    case prop of
        (*Implicacion y disyuncion*)
        implicacion (prop1, prop2)              => if prop1 <> prop2 then ~:(simpl prop1) :||: (simpl prop2)
                                                   else prop 

        (*De Morgan Disyuncion*)
    |   negacion(disyuncion(prop1, prop2))     => conjuncion(simpl(negacion(prop1)), simpl(negacion(prop2)))


        (*De Morgan Conjuncion*)
    |   negacion(conjuncion(prop1, prop2))     => disyuncion(simpl(negacion(prop1)), simpl(negacion(prop2)))


        (*Neutro con disyuncion*)
    |   disyuncion (prop1, constante false)     => simpl prop1

    |   disyuncion (constante false, prop2)     => simpl prop2

    |   disyuncion (negacion(prop1), constante false)     => simpl (negacion(prop1))
    
    |   disyuncion (constante false, negacion(prop2))     => simpl (negacion(prop2))

        (*Neutro con conjuncion*)
    |   conjuncion (prop1, constante true)     => simpl prop1

    |   conjuncion (constante true, prop2)     => simpl prop2

    |   conjuncion (negacion(prop1), constante true)     => simpl (negacion(prop1))

    |   conjuncion (constante true, negacion(prop2))     => simpl (negacion(prop2))

        (*Dominacion con Verdadero*)
    |   disyuncion(prop1, constante true)      => constante true

    |   disyuncion(constante true, prop2)      => constante true


            (*Dominacion con False*)

    |   disyuncion(negacion(prop1), constante true)      => if prop1 = negacion(prop1) then constante true else prop

    |   disyuncion(constante true, negacion(prop2))      => if prop2 = negacion(prop2) then constante true else prop

        (*Dominacion con False*)

    |   conjuncion(prop1, constante false)      => constante false

    |   conjuncion(constante false, prop2)      => constante false


            (*Inversos con verdadero*)
    |   disyuncion  (prop1, negacion(prop2))    => if prop1 = prop2 then constante true
                                                   else prop

    |   disyuncion  (negacion(prop1), prop2)    => if prop1 = prop2 then constante true
                                                   else prop

        (*Inversos con falso*)
    |   conjuncion  (prop1, negacion(prop2))    => if prop1 = prop2 then constante false
                                                   else prop

    |   conjuncion  (negacion(prop1), prop2)    => if prop1 = prop2 then constante false
                                                   else prop

    |   conjuncion(negacion(prop1), constante false)      => constante false

    |   conjuncion(constante false, negacion(prop2))      => constante false


        (*Idempotencia*)
    |   disyuncion (prop1, prop2)              => if prop1 = prop2 then simpl prop1
                                                  else prop

    |   conjuncion (prop1, prop2)              => if prop1 = prop2 then simpl prop1
                                                  else prop


    |   disyuncion (negacion(prop1), negacion(prop2))              => if prop1 = prop2 then simpl (negacion(prop1))
                                                  else prop

    |   conjuncion (negacion(prop1), negacion(prop2))              => if prop1 = prop2 then simpl (negacion(prop1))
                                                  else prop

        (*Doble negacion*)
    |   negacion(negacion(prop1))              => simpl prop1

        (*Casos base*)

    | variable nombre                          => prop

    | constante true                           => prop

    | constante false                          => prop   

;

