module HOPPER-SYNTAX 
    import DOMAINS

    syntax Pgm ::= "program" "{" Block "}"      

    syntax Skip ::= "Skip"

    syntax Block ::= "{" Stmt "}" 
                | Stmt

    syntax Stmt ::= "if" "(" BExp ")" Block [strict(1)]
                | "if" "(" BExp ")" Block ElseIfStmt [strict(1)]
                | BExp "?" Block ":" Block [strict(1)]
                | "while" "(" BExp ")" Block
                | "do" Block "while" "(" BExp ")"
                | "for" "(" Type UniqueIdAssigner ";" BExp ";" AExpMod ")" Block
                | Foreach
                | AExp
                | DecVar ";"
                | FuncDec
                | FuncCall ";"
                | Assigner
                | AExpMod
                | Skip
                | Stmt Stmt [left]


    syntax Params ::= List{Id, ","}
    syntax FuncDec ::= "function" Id "(" Params ")" Block
    syntax Values ::= List{Int, ","}
    syntax FuncCall ::= Id "(" Values ")"
    syntax Local ::= "local" "(" Id "," Stmt ")"

    syntax ListValues ::= List{Int, ","}
    syntax ArrayList ::= "[" ListValues "]"
    syntax Foreach ::= "foreach" "(" Id "in" ArrayList ")" Block
    
    syntax Type ::= "integer" | "boolean"

    syntax Ids ::= List{Id, ","}
    
    syntax DecVar ::= Type Ids

    syntax UniqueIdAssigner ::= Id "=" AExp  [strict(2)]

    syntax Assigner ::= DecVar "=" AExp ";" [strict(2)]
                    |  UniqueIdAssigner

    syntax ElseIfStmt ::= "elif" "(" BExp ")" Block
                        | "else" Block
                        | "elif" "(" BExp ")" Block ElseIfStmt

    syntax BExp ::= Bool
                    | AExp "<" AExp [strict]
                    | AExp "<=" AExp [strict]
                    | AExp ">" AExp [strict]
                    | AExp ">=" AExp [strict]
                    | "(" BExp ")" [bracket]


    syntax AExpMod ::= Id "++" 
    syntax AExp ::= Int
                | Id
                > left: AExp "*" AExp [seqstrict]
                > left: AExp "/" AExp [seqstrict]
                | AExp "-" AExp [seqstrict]
                | AExp "+" AExp [seqstrict]
                | "(" AExp ")" [bracket]
                
                

    rule program { B:Block } => B [structural]
 
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]
    rule local(I:Id, S1:Stmt S2:Stmt) => local(I, S1) ~> local(I, S2) [structural]
    
    rule Skip => .
    
    rule if (true) { S:Stmt } => S
    rule if (false) { _ } => Skip
    rule if (true) { B } S:ElseIfStmt => B
    rule if (false) { _ } S:ElseIfStmt => S
    rule elif ( B:BExp ) { S1:Stmt } S2:ElseIfStmt => if ( B ) { S1 } S2
    rule elif ( B:BExp ) { S:Stmt } => if ( B ) { S }
    rule else { S } => S

    rule true ? B:Block : _ => B 
    rule false ? _ : B:Block => B

    rule while (B:BExp) { S:Stmt } => if(B){ S while (B) { S } } [structural]
    
    rule do { S:Stmt } while (B:BExp) => S ~> if(B){ do { S } while (B) } [structural]
    
    rule for (T:Type I:Id = V:AExp ; B:BExp ; Amod:AExpMod ) {S} 
        => T I = V ; ~> while (B) { S Amod } [structural]

    rule <k>
            foreach (I:Id in [ (V:Int, Vs:ListValues) ] ) { S:Stmt }
            => S ~> foreach (I in [ Vs:ListValues ] ) { S }
            ... 
        </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
        when notBool (I in keys(MEnv))

    rule <k>
            foreach (I:Id in [ (V:Int, Vs:ListValues) ] ) { S:Stmt }
            => S ~> foreach (I in [ Vs:ListValues ] ) { S }
            ... 
        </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    rule foreach (I:Id in [ .ListValues ] ) B:Block => Skip
        
    rule I1:Int + I2:Int => I1 +Int I2
    rule I1:Int - I2:Int => I1 -Int I2
    rule I1:Int * I2:Int => I1 *Int I2
    rule I1:Int / I2:Int => I1 /Int I2
    rule I1:Int < I2:Int => I1 <Int I2
    rule I1:Int <= I2:Int => I1 <=Int I2
    rule I1:Int > I2:Int => I1 >Int I2

    rule <k> T:Type I:Id ; => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>
                    
    rule <k> T:Type (I:Id, Xs:Ids) ; => T Xs ; ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> T:Type (I:Id, Xs:Ids) = V:Int ; => T Xs = V ; ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule T:Type .Ids ; => Skip  
    rule T:Type .Ids = _:Int ; => Skip  

    rule <k> integer I:Id = V:Int ; => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> I:Id = V:Int => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    rule <k> I1:Id = I2:Id => I1 = V ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V  ... </store>

    rule <k> I:Id => V ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> V ... </store>

    rule <k> I:Id ++ => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (V => V +Int 1) ... </store>

    rule <k> function I:Id (P:Params) { S:Stmt } => Skip ... </k>
        ( .Bag => <thread> 
                <id> I </id>
                <scope> S </scope>
                <params> P </params>
                <temp> P </temp>
                <localEnv> .Map </localEnv>
            </thread>
        )

    rule <k> I:Id (.Values) ; => local(I, S) ... </k>
        <thread>
            ...
            <id> I </id>
            <scope> S:Stmt </scope>
            <params> P </params> 
            <temp> (.Params => P) </temp> 
            ...
        </thread>
    
    rule <k> I:Id ((V:Int, Vs:Values)) ; => I:Id (Vs) ; ... </k>
        <thread>
            ...
            <id> I </id>
            <temp> ((P:Id, Ps:Params) => Ps)  </temp>
            <localEnv> Rho:Map => Rho P |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>
        
    rule <k> local(FuncId:Id, integer I:Id = V:Int ;) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>



    configuration <T>
        <k> $PGM:Pgm </k>
        <functions color="orange"> 
            <thread multiplicity="*" color="blue" type="Map"> 
                <id> .K </id>
                <scope> .K </scope>
                <params> .K </params>
                <temp> .K </temp>
                <localEnv> .Map </localEnv>
            </thread> 
        </functions>
        <env> .Map </env>
        <store> .Map </store>
        <loc> 1 </loc>
    </T>
 
endmodule

module HOPPER
    import DOMAINS
    import HOPPER-SYNTAX

    syntax KResult ::= Int | Bool
endmodule