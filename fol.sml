structure FOL =
struct

    datatype term = VAR of string
                    | FUN of string * term list
                    | CONST of string

    datatype Pred = FF
                    | ATOM of string * term list
                    | NOT of Pred
                    | AND of Pred * Pred
                    | OR of Pred * Pred
                    | COND of Pred * Pred
                    | BIC of Pred * Pred
                    | ITE of Pred * Pred * Pred
                    | ALL of term * Pred
                    | EX of term * Pred

    datatype Argument = HENCE of Pred list * Pred

    exception NotVAR
    exception NotWFT
    exception NotWFP
    exception NotWFA
    exception NotClosed

    datatype tableauTree = EMPTY
                           | TREE of Pred * tableauTree * tableauTree

    fun substituteTerm(t,x,te) = 
    case te of
    VAR(y)      => if x=te then t else te
    | CONST(a)  => te
    | FUN(y,tl) => FUN(y,List.map (fn i => substituteTerm(t,x,i)) tl)

    fun substituteVariable(t,x,pred) = 
    case pred of
    FF              => FF
    | NOT(p)        => NOT(substituteVariable(t,x,p))
    | AND(p,q)      => AND(substituteVariable(t,x,p),substituteVariable(t,x,q))
    | OR(p,q)       => OR(substituteVariable(t,x,p),substituteVariable(t,x,q))
    | COND(p,q)     => COND(substituteVariable(t,x,p),substituteVariable(t,x,q))
    | BIC(p,q)      => BIC(substituteVariable(t,x,p),substituteVariable(t,x,q))
    | ITE(p,q,r)    => ITE(substituteVariable(t,x,p),substituteVariable(t,x,q),substituteVariable(t,x,r))
    | ALL(y,p)      => if y = x then pred else if y = t then 
                        let
                            val z = VAR("newVar") 
                        in 
                            ALL(z,substituteVariable(t,x,substituteVariable(z,t,p)))
                        end
                        else ALL(y,substituteVariable(t,x,p))
    | EX(y,p)       => if y = x then pred else if y = t then 
                        let
                            val z = VAR("newVar") 
                        in 
                            EX(z,substituteVariable(t,x,substituteVariable(z,t,p)))
                        end
                        else EX(y,substituteVariable(t,x,p))
    | ATOM(y,tl)    => ATOM(y,List.map (fn i => substituteTerm(t,x,i)) tl)

    fun substitute(t,x,pred) = 
    (case x of
        VAR(y)  => (case t of
                    VAR(z)          => if y = z then pred else substituteVariable(t,x,pred)
                    | FUN(f,ts)     => substituteVariable(t,x,pred)
                    | CONST(c)      => substituteVariable(t,x,pred))
        | _     => raise NotVAR)

    fun checkAtom(atom,[]) = false
    | checkAtom(atom,a::atomList) = if (atom = a) then true else checkAtom(atom,atomList)

    fun explodeTerms([],x,pred) = []
    | explodeTerms(t::termList,x,pred) = 
    let
        val newList = case t of 
                      FUN(f,tl) => tl@termList
                      | _       => termList
    in
        substitute(t,x,pred)::explodeTerms(newList,x,pred)
    end

    fun explodeAtoms([],x,pred) = []
    | explodeAtoms(atom::atomList,x,pred) = 
    case atom of
    ATOM(s,tl)          => explodeTerms(tl,x,pred)@explodeAtoms(atomList,x,pred)
    | NOT(ATOM(s,tl))   => explodeTerms(tl,x,pred)@explodeAtoms(atomList,x,pred)
    | _                 => raise NotWFT

    fun CreateTableau([],atomList,[],depth) = EMPTY
    | CreateTableau([],atomList,allPred::allList,depth) =
    (case allPred of
    ALL(x,p)                    => CreateTableau(explodeAtoms(atomList,x,p),atomList,allList@[allPred],depth)
    | _                         => raise NotWFP)
    | CreateTableau(pred::predList,atomList,allList,depth) =
    case pred of
    FF                          => TREE(FF,EMPTY,EMPTY)
    | ATOM(s,ls)                => if checkAtom(NOT(pred),atomList) then TREE(pred,TREE(FF,EMPTY,EMPTY),EMPTY)
                                   else if checkAtom(pred,atomList) then CreateTableau(predList,atomList,allList,depth)
                                   else TREE(pred,CreateTableau(predList,pred::atomList,allList,depth+1),EMPTY)
    | AND(p,q)                  => TREE(pred,CreateTableau(p::q::predList,atomList,allList,depth+1),EMPTY)
    | OR(p,q)                   => TREE(pred,CreateTableau(p::predList,atomList,allList,depth+1),CreateTableau(q::predList,atomList,allList,depth+1))
    | COND(p,q)                 => TREE(pred,CreateTableau(NOT(p)::predList,atomList,allList,depth+1),CreateTableau(q::predList,atomList,allList,depth+1))
    | BIC(p,q)                  => TREE(pred,CreateTableau(COND(p,q)::COND(q,p)::predList,atomList,allList,depth+1),EMPTY)
    | ITE(p,q,r)                => TREE(pred,CreateTableau(p::q::predList,atomList,allList,depth+1),CreateTableau(NOT(p)::r::predList,atomList,allList,depth+1))
    | NOT(p)                    => (case p of
                                    ATOM(a)         => if checkAtom(p,atomList) then TREE(pred,TREE(FF,EMPTY,EMPTY),EMPTY)
                                                       else if checkAtom(NOT(p),atomList) then CreateTableau(predList,atomList,allList,depth)
                                                       else TREE(pred,CreateTableau(predList,pred::atomList,allList,depth+1),EMPTY) 
                                    | NOT(a)        => CreateTableau(a::predList,atomList,allList,depth)
                                    | AND(a,b)      => TREE(pred,CreateTableau(NOT(a)::predList,atomList,allList,depth+1),CreateTableau(NOT(b)::predList,atomList,allList,depth+1))
                                    | OR(a,b)       => TREE(pred,CreateTableau(NOT(a)::NOT(b)::predList,atomList,allList,depth+1),EMPTY)
                                    | COND(a,b)     => TREE(pred,CreateTableau(a::NOT(b)::predList,atomList,allList,depth+1),EMPTY)
                                    | BIC(a,b)      => TREE(pred,CreateTableau(NOT(COND(a,b))::predList,atomList,allList,depth+1),CreateTableau(NOT(COND(b,a))::predList,atomList,allList,depth+1))
                                    | ITE(a,b,c)    => TREE(pred,CreateTableau(OR(NOT(a),NOT(b))::OR(a,NOT(c))::predList,atomList,allList,depth+1),EMPTY)
                                    | ALL(x,p)      => let
                                                            val freshTerm = CONST("b"^Int.toString(depth))
                                                            val freshName = "a"^Int.toString(depth)
                                                            val freshAtom = ATOM(freshName,[freshTerm])
                                                            val newList = substitute(freshTerm,x,NOT(p))::predList
                                                        in
                                                            TREE(pred,CreateTableau(newList,freshAtom::atomList,allList,depth+1),EMPTY)
                                                        end
                                    | EX(x,p)       => TREE(pred,CreateTableau(predList,atomList,ALL(x,NOT(p))::allList,depth+1),EMPTY)
                                    | _             => raise NotWFP)
    | EX(x,p)                   =>  let
                                        val freshTerm = CONST("b"^Int.toString(depth))
                                        val freshName = "a"^Int.toString(depth)
                                        val freshAtom = ATOM(freshName,[freshTerm])
                                        val newList = substitute(freshTerm,x,p)::predList
                                    in 
                                        TREE(pred,EMPTY,CreateTableau(newList,freshAtom::atomList,allList,depth+1))
                                    end
    | ALL(x,p)                  =>  TREE(pred,CreateTableau(predList,atomList,pred::allList,depth+1),EMPTY)


    getDotFromTableau(tableau) = 
    

    fun mktableau(predlist:Pred list,pred:Pred) : tableauTree =
    let 
        val newList = NOT(pred)::predlist
        val outstream = TextIO.openOut "tableau.dot"
        val tableau = CreateTableau(newList,[],[],0)
        val tableauOutput = getDotFromTableau(tableau)
    in
        (* (TextIO.output(outstream,tableauOutput);TextIO.closeOut(outstream)) *)
        tableau
    end

    fun getTableau(arg) = 
    case arg of
    HENCE(predlist,pred)    => mktableau(predlist,pred)

end