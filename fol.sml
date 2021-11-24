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
                      FUN(f,tl)  => tl@termList
                      | VAR(y)   => raise NotClosed
                      | CONST(c) => termList
    in
        substitute(t,x,pred)::explodeTerms(newList,x,pred)
    end

    fun explodeChildTerms([],x,pred,id) = []
    | explodeChildTerms(t::termList,x,pred,id) =
    let
        val newList = case t of 
                        FUN(f,tl)   => tl@termList
                        | VAR(y)    => raise NotClosed
                        | CONST(c)  => termList
    in
        (substitute(t,x,pred),id)::explodeChildTerms(newList,x,pred,id)
    end

    fun explodeAtoms([],x,pred) = []
    | explodeAtoms(atom::atomList,x,pred) = 
    case atom of
    ATOM(s,tl)          => explodeTerms(tl,x,pred)@explodeAtoms(atomList,x,pred)
    | NOT(ATOM(s,tl))   => explodeTerms(tl,x,pred)@explodeAtoms(atomList,x,pred)
    | _                 => raise NotWFT

    fun explodeChildAtoms([],x,pred,id) = []
    | explodeChildAtoms((atom,_)::atomList,x,pred,id) = 
    case atom of
    ATOM(s,tl)          => explodeChildTerms(tl,x,pred,id)@explodeChildAtoms(atomList,x,pred,id)
    | NOT(ATOM(s,tl))   => explodeChildTerms(tl,x,pred,id)@explodeChildAtoms(atomList,x,pred,id)
    | _                 => raise NotWFT

    fun CreateTableau([],atomList,[],depth) = EMPTY
    | CreateTableau([],atomList,allPred::allList,depth) =
    (case allPred of
    ALL(x,p)                    => TREE(allPred,CreateTableau(explodeAtoms(atomList,x,p),atomList,allList@[allPred],depth+1),EMPTY)
    | _                         => raise NotWFP)
    | CreateTableau(pred::predList,atomList,allList,depth) =
    case pred of
    FF                          => raise NotWFP
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
                                    | ALL(x,b)      =>  let
                                                            val freshTerm = CONST("b"^Int.toString(depth))
                                                            val freshName = "a"^Int.toString(depth)
                                                            val freshAtom = ATOM(freshName,[freshTerm])
                                                            val newList = substitute(freshTerm,x,NOT(b))::predList
                                                        in
                                                            (case x of 
                                                            VAR(y)      => TREE(pred,CreateTableau(newList,freshAtom::atomList,allList,depth+1),EMPTY)
                                                            | _         => raise NotVAR)
                                                        end
                                    | EX(x,b)       => (case x of
                                                        VAR(y)      => CreateTableau(predList,atomList,ALL(x,NOT(b))::allList,depth)
                                                        | _         => raise NotVAR)
                                    | _             => raise NotWFP)
    | EX(x,p)                   =>  let
                                        val freshTerm = CONST("b"^Int.toString(depth))
                                        val freshName = "a"^Int.toString(depth)
                                        val freshAtom = ATOM(freshName,[freshTerm])
                                        val newList = substitute(freshTerm,x,p)::predList
                                    in 
                                        case x of
                                        VAR(y)   => TREE(pred,CreateTableau(newList,freshAtom::atomList,allList,depth+1),EMPTY)
                                        | _      => raise NotVAR
                                    end
    | ALL(x,p)                  =>  (case x of
                                    VAR(y)     => CreateTableau(predList,atomList,pred::allList,depth)
                                    | _        => raise NotVAR)

    fun findAtom(atom,[]) = (false,"")
    | findAtom(atom,(a,idx)::atomList) = if (a = atom) then (true,idx) else findAtom(atom,atomList)

    fun reverseList([],answer) = answer
    | reverseList(ls::result,answer) = reverseList(result,ls::answer)

    fun findParent(pred,[],isValid,parentIndex,result) = (isValid,reverseList(result,[]),parentIndex)
    | findParent(pred,(p,idx)::parentList,isValid,parentIndex,result) = 
    if (p=pred) then findParent(pred,parentList,true,idx,result) else findParent(pred,parentList,isValid,parentIndex,(p,idx)::result)


    fun printTerm(t) =
    case t of
    VAR(y)          => y
    | CONST(c)      => c
    | FUN(f,ls)     => f^"("^printTermList(ls)^")"

    and printTermList([]) = ""
    | printTermList(t::[]) = printTerm(t)
    | printTermList(t::ls) = printTerm(t)^","^printTermList(ls)

    fun printPred(pred) = 
    case pred of
    FF                      => "\\bot"
    | ATOM(s,ls)            => s^"("^printTermList(ls)^")"
    | AND(p,q)              => printPred(p)^" \\wedge "^printPred(q)
    | OR(p,q)               => printPred(p)^" \\vee "^printPred(q)
    | COND(p,q)             => printPred(p)^" \\too "^printPred(q)
    | BIC(p,q)              => printPred(p)^" \\leftrightarrow "^printPred(q)
    | ITE(p,q,r)            => "if "^printPred(p)^" then "^printPred(q)^" else "^printPred(r)
    | NOT(p)                => "\\neg "^printPred(p)
    | EX(x,p)               => "\\exists "^printTerm(x)^"["^printPred(p)^"]"
    | ALL(x,p)              => "\\forall "^printTerm(x)^"["^printPred(p)^"]"

    fun printNode(pred,id) = "\t"^id^" [texlbl=\"\\underline{$"^printPred(pred)^"$ }\"];\n"

    fun printRecursive(EMPTY,atomList,parentList,id) = ("","","","")
    | printRecursive(TREE(pred,left,right),atomList,parentList,id) = 
    let
        val nodes = printNode(pred,id) 
        val edges = 
        case left of 
        EMPTY                   => ""
        | _                     =>
        (case pred of
        FF                      => ""
        | ATOM(s,ls)            => "\t\t"^id^" -> "^id^"1;\n"
        | AND(p,q)              => "\t\t"^id^" -> "^id^"1;\n"
        | OR(p,q)               => "\t\t"^id^" -> "^id^"1;\n"^"\t\t"^id^" -> "^id^"2;\n"
        | COND(p,q)             => "\t\t"^id^" -> "^id^"1;\n"^"\t\t"^id^" -> "^id^"2;\n"
        | BIC(p,q)              => "\t\t"^id^" -> "^id^"1;\n"
        | ITE(p,q,r)            => "\t\t"^id^" -> "^id^"1;\n"^"\t\t"^id^" -> "^id^"2;\n"
        | EX(x,p)               => "\t\t"^id^" -> "^id^"1;\n"
        | ALL(x,p)              => "\t\t"^id^" -> "^id^"1;\n"
        | NOT(p)                => (case p of
                                    ATOM(a)             => "\t\t"^id^" -> "^id^"1;\n"
                                    | AND(a,b)          => "\t\t"^id^" -> "^id^"1;\n"^"\t\t"^id^" -> "^id^"2;\n"
                                    | OR(a,b)           => "\t\t"^id^" -> "^id^"1;\n"
                                    | COND(a,b)         => "\t\t"^id^" -> "^id^"1;\n"
                                    | BIC(a,b)          => "\t\t"^id^" -> "^id^"1;\n"^"\t\t"^id^" -> "^id^"2;\n"
                                    | ITE(a,b,c)        => "\t\t"^id^" -> "^id^"1;\n"
                                    | EX(x,b)           => "\t\t"^id^" -> "^id^"1;\n"
                                    | ALL(x,b)          => "\t\t"^id^" -> "^id^"1;\n"
                                    | _                 => raise NotWFP))
        val (redEdges,newAtomList) = 
        case pred of
        ATOM(s,ls)            => let val (isPresent,idx) = findAtom(NOT(pred),atomList) in if isPresent then ("\t\t"^id^" -> "^idx^";\n",atomList) else ("",(pred,id)::atomList) end
        | NOT(ATOM(s,ls))     => let val (isPresent,idx) = findAtom(ATOM(s,ls),atomList) in if isPresent then ("\t\t"^id^" -> "^idx^";\n",atomList) else ("",(pred,id)::atomList) end
        | _                   => ("",atomList)
        val (blueEdges,newParentList) =
        let
            val (isPresent,result,idx) = findParent(pred,parentList,false,"",[])
            val updatedBlueEdges = if isPresent then "\t\t"^idx^" -> "^id^";\n" else ""
            val updatedParentList = 
            case pred of
            AND(p,q)                => (q,id)::result
            | BIC(p,q)              => (COND(q,p),id)::result
            | ALL(x,p)              => explodeChildAtoms(atomList,x,p,id)@result
            | NOT(p)                => (case p of
                                       OR(a,b)          => (NOT(b),id)::result
                                       | COND(a,b)      => (NOT(b),id)::result
                                       | ITE(a,b,c)     => (OR(a,NOT(c)),id)::result
                                       | EX(x,b)        => explodeChildAtoms(atomList,x,NOT(b),id)@result
                                       | _              => result)
            | _                     => result
        in
            (updatedBlueEdges,updatedParentList)
        end 
        val (nodes1,edges1,blueEdges1,redEdges1) = printRecursive(left,newAtomList,newParentList,id^"1")
        val (nodes2,edges2,blueEdges2,redEdges2) = printRecursive(right,newAtomList,newParentList,id^"2")
    in 
        (nodes^nodes1^nodes2,edges^edges1^edges2,blueEdges^blueEdges1^blueEdges2,redEdges^redEdges1^redEdges2)
    end                      

    fun getDotFromTableau(tableau) = 
    let
        val (nodes,edges,blueEdges,redEdges) = printRecursive(tableau,[],[],"1")
    in
        "digraph{\n\tnodesep = 0.5;\n\tranksep = 0.20;\n\tnode [shape=plaintext];\n"^nodes^"\tsubgraph dir{\n"^edges^"\t}\n"^
        "\tsubgraph ancestor{\n\t\tedge [dir=back, color=blue style=dashed];\n"^blueEdges^"\t}\n"^ 
        "\tsubgraph undir{\n\t\tedge [dir=none, color=red];\n"^redEdges^"\t}\n"^"}" 
    end

    fun mktableau(predlist:Pred list,pred:Pred) : unit =
    let 
        val newList = NOT(pred)::predlist
        val outstream = TextIO.openOut "tableau.dot"
        val tableau = CreateTableau(newList,[],[],0)
        val tableauOutput = getDotFromTableau(tableau)
    in
        (TextIO.output(outstream,tableauOutput);TextIO.closeOut(outstream))
    end

    fun getTableau(arg) = 
    case arg of
    HENCE(predlist,pred)    => mktableau(predlist,pred)

end

open FOL;