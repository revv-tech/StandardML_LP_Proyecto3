
val p = variable "p";
val q = variable "q";
val z = variable "z";
val f = constante false;
val t = constante true;

(* PRUEBA PARA SIMPL*)
val hitotsu = (p :&&: p) :=>: (q :||: (~:q))
val futatsu = ~:(~:p :||: f)
val mittsu = ((~:(p) :||: f) :=>: (q :&&: t))


(*PRUEBA de FND*)
val fndp1 =  ~:(variable ("p"):||:variable ("q")):=>:(variable ("p"):=>:variable ("r"))
val fndp2 =  (variable ("p") :&&: variable ("r")) :<=>: (variable ("q") :||: variable ("r"))
val fndp3 =  ((variable ("p") :&&: variable ("r")) :||: ( variable ("q") :&&: ~: (variable ("r"))))

(*PRUEBA PARA BONITA*)
val bonita1 = (p :||: q) :=>: (p :&&: t)
val bonita2 = f :<=>: ~:(p :&&: q)