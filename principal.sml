use "sintax.sml";
use "vars.sml";
use "gen_bools.sml";
use "as_vals.sml";
use "evalProp.sml";
use "taut.sml";


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



