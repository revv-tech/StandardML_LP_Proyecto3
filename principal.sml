use "sintax.sml";
use "vars.sml";
use "gen_bools.sml";
use "as_vals.sml";
use "evalProp.sml";
use "taut.sml";




fun fndFALSE prop = 

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
		
    in
    	fndAux listaBooleanos
    end
;

(*RECIBE LISTA DE LISTAS GRANDE*)
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
;

fun amountVars (listVars) = 
	val n = length listVars
	case n of 
		0 => []
		| 1 => [List.nth(listVars,0)];
		| 2 => [List.nth(listVars,0) :&&: [List.nth(listVars,1)];
		| 3 => [List.nth(listVars,0) :&&: [List.nth(listVars,1) :&&: [List.nth(listVars,2)];
		| 4 => [List.nth(listVars,0) :&&: [List.nth(listVars,1) :&&: [List.nth(listVars,2) :&&: [List.nth(listVars,3)];
		| 5 => List.nth(listVars,0) :&&: List.nth(listVars,1) :&&: List.nth(listVars,2) :&&: List.nth(listVars,3) :&&: List.nth(listVars,4)];
		| 6 => List.nth(listVars,0) :&&: List.nth(listVars,1) :&&: List.nth(listVars,2) :&&: List.nth(listVars,3) :&&: List.nth(listVars,4) :&&: List.nth(listVars,5)];
;

fun addSign [] = []
	| addSign (lista :: mas_listas) = 
		let
			fun addSignAux [] = []
			| addSignAux( par) = 
				let
					val p1 = List.nth(par,0)
					val p2 =  List.nth(par,1)
					val tmp = p1 :&&: p2
				in
					[tmp]
				end
 				
		in 
			addSignAux lista @ addSign mas_listas
		end
;



fun imprimirFnd prop =
	case prop of
        constante false             => "false"
    |   constante true              => "true"
    |   variable nombre             => nombre
    |   negacion prop1              => "negación (" ^ imprimir  prop1 ^ ")"
    |   conjuncion (prop1, prop2)   => "conjuncion (" ^ imprimir prop1 ^ ", " ^ imprimir prop2 ^ ")"
    |   disyuncion (prop1, prop2)   => "disyuncion (" ^ imprimir prop1 ^ ", " ^ imprimir prop2 ^ ")"
    |   implicacion (prop1, prop2)  => "implicacion (" ^ imprimir prop1 ^ ", " ^ imprimir prop2 ^ ")"
    |   equivalencia (prop1, prop2) => "equivalencia (" ^ imprimir prop1 ^ ", " ^ imprimir prop2 ^ ")"
;



