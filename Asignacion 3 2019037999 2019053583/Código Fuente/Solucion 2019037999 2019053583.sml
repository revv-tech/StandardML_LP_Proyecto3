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
        fun gen_cony [] = constante true
            | gen_cony ([prop]) = prop
            | gen_cony (var :: mas_variables) =  
                (conjuncion (var ,gen_cony(mas_variables)))
        
        fun gen_disy [] = constante false
            | gen_disy ([prop]) = prop
            | gen_disy (var :: mas_variables) =  
                (disyuncion (var ,gen_disy (mas_variables)))

        val tmp = fndAux listaBooleanos
        val tmp2 = toProp tmp
        val newGC = map gen_cony
        val tmp3 = newGC tmp2
        val tmpFinal = gen_disy tmp3
    
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
    |   negacion prop1              => "~(" ^ bonita  prop1 ^ ")"
    |   conjuncion (prop1, prop2)   => "(" ^ bonita prop1 ^ " /\\ " ^ bonita prop2 ^ ")"
    |   disyuncion (prop1, prop2)   => "(" ^ bonita prop1 ^ " \\/ " ^ bonita prop2 ^ ")"
    |   implicacion (prop1, prop2)  => "(" ^ bonita prop1 ^ " => " ^ bonita prop2 ^ ")"
    |   equivalencia (prop1, prop2) => "(" ^ bonita prop1 ^ " <=> " ^ bonita prop2 ^ ")"
;

(*SIMPLIFICACION*)
fun simpl prop =

    case prop of
        (*Implicacion y disyuncion*)
        implicacion (prop1, prop2)              => if prop1 <> prop2 then simpl (~:(simpl prop1) :||: (simpl prop2))
                                                   else prop

        (*Neutro con disyuncion*)
    |   disyuncion (prop1, constante false)     => simpl prop1

    |   disyuncion (constante false, prop2)     => simpl prop2


        (*Neutro con conjuncion*)
    |   conjuncion (prop1, constante true)     => simpl prop1

    |   conjuncion (constante true, prop2)     => simpl prop2


        (*Dominacion con Verdadero*)
    |   disyuncion(prop1, constante true)      => constante true

    |   disyuncion(constante true, prop2)      => constante true


            (*Dominacion con False*)
    |   conjuncion(prop1, constante false)      => constante false

    |   conjuncion(constante false, prop2)      => constante false


            (*Inversos con verdadero*)
    |   disyuncion  (prop1, negacion(prop2))    => if prop1 = prop2 then constante true
                                                   else disyuncion  (simpl prop1, simpl (negacion(prop2)))

    |   disyuncion  (negacion(prop1), prop2)    => if prop1 = prop2 then constante true
                                                   else disyuncion  (simpl(negacion(prop1)), simpl prop2)

        (*Inversos con falso*)
    |   conjuncion  (prop1, negacion(prop2))    => if prop1 = prop2 then constante false
                                                   else conjuncion (simpl prop1, simpl (negacion(prop2)))

    |   conjuncion  (negacion(prop1), prop2)    => if prop1 = prop2 then constante false
                                                   else conjuncion (simpl (negacion(prop1)), simpl prop2)

        (*Idempotencia*)
    |   disyuncion (prop1, prop2)              => if prop1 = prop2 then simpl prop1
                                                  else disyuncion (simpl prop1, simpl prop2)

    |   conjuncion (prop1, prop2)              => if prop1 = prop2 then simpl prop1
                                                  else conjuncion (simpl prop1, simpl prop2)


        (*Doble negacion*)
    |   negacion(negacion(prop1))              => simpl prop1

        (*Casos base*)

    | negacion(prop1)                          => simpl prop1

    | variable nombre                          => prop

    | constante true                           => prop

    | constante false                          => prop
    


;
