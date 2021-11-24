structure tableau =
struct 

open AST

fun checkAtom(atom,[]) = false
| checkAtom(atom,a::atomList) = if (atom = a) then true else checkAtom(atom,atomList)

fun checkTableau([],atomList) = (false,atomList)
| checkTableau(prop::proplist,atomList) =
case prop of
ATOM(a)             => if checkAtom(NOT(prop),atomList) then (true,[]) else if checkAtom(prop,atomList) then checkTableau(proplist,atomList)
                       else checkTableau(proplist,prop::atomList)
| AND(a,b)          => checkTableau(a::b::proplist,atomList)
| OR(a,b)           =>  let
                            val (truthVal1,atoms1) = checkTableau(a::proplist,atomList) 
                            val (truthVal2,atoms2) = checkTableau(b::proplist,atomList)
                        in
                            if truthVal1 = false then (truthVal1,atoms1) 
                            else if truthVal2 = false then (truthVal2,atoms2)
                            else (true,[]) 
                        end
| COND(a,b)         =>  let
                            val (truthVal1,atoms1) = checkTableau(NOT(a)::proplist,atomList) 
                            val (truthVal2,atoms2) = checkTableau(b::proplist,atomList)
                        in
                            if truthVal1 = false then (truthVal1,atoms1) 
                            else if truthVal2 = false then (truthVal2,atoms2)
                            else (true,[]) 
                        end 
| BIC(a,b)          => checkTableau(COND(a,b)::COND(b,a)::proplist,atomList)
| ITE(a,b,c)        =>  let
                            val (truthVal1,atoms1) = checkTableau(a::b::proplist,atomList)
                            val (truthVal2,atoms2) = checkTableau(NOT(a)::c::proplist,atomList)
                        in
                            if truthVal1 = false then (truthVal1,atoms1) 
                            else if truthVal2 = false then (truthVal2,atoms2)
                            else (true,[]) 
                        end
| NOT(p)            => case p of
                       ATOM(a)        => if checkAtom(p,atomList) then (true,[]) else if checkAtom(NOT(p),atomList) then checkTableau(proplist,atomList)
                                         else checkTableau(proplist,prop::atomList)
                       | NOT(a)       => checkTableau(a::proplist,atomList)  
                       | AND(a,b)     => let
                                            val (truthVal1,atoms1) = checkTableau(NOT(a)::proplist,atomList)
                                            val (truthVal2,atoms2) = checkTableau(NOT(b)::proplist,atomList)
                                         in
                                            if truthVal1 = false then (truthVal1,atoms1) 
                                            else if truthVal2 = false then (truthVal2,atoms2)
                                            else (true,[]) 
                                         end 
                       | OR(a,b)      => checkTableau(NOT(a)::NOT(b)::proplist,atomList)
                       | COND(a,b)    => checkTableau(a::NOT(b)::proplist,atomList)
                       | BIC(a,b)     => let
                                            val (truthVal1,atoms1) = checkTableau(NOT(COND(a,b))::proplist,atomList)
                                            val (truthVal2,atoms2) = checkTableau(NOT(COND(b,a))::proplist,atomList)
                                         in
                                            if truthVal1 = false then (truthVal1,atoms1) 
                                            else if truthVal2 = false then (truthVal2,atoms2)
                                            else (true,[]) 
                                         end 
                       | ITE(a,b,c)   => checkTableau(OR(NOT(a),NOT(b))::OR(a,NOT(c))::proplist,atomList) 

fun checkValidity arg =
let
    val proplist = case arg of HENCE(pl,p) => NOT(p)::pl
in
    checkTableau(proplist,[])
end

end