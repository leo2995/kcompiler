module GO-SYNTAX
import DOMAINS
syntax pgm ::= "func main()" "{" Block "}" 

syntax Skip ::= "Skip"

syntax Block ::= "{"Stmt"}"


|Stmt

syntax Stmt ::= "if" "(" BExp ")" Block [strict(1)]
                | "if" "(" BExp ")" Block ElseIfStmt [strict(1)]
                |"forp1" "(" BExp ")" Block
                | "for" "(" "var" UniqueIdAssigner ";" BExp ";" AExpMod ")" Block
                | AExp
                | DecVar ";"
                | FuncDec
                | FuncCall ";"
                | Assigner
                | AExpMod
                | Skip
                | Stmt Stmt [left]

syntax ElseIfStmt ::= "else" "if" "(" BExp ")" Block
                        | "else" Block
                        | "else" "if" "(" BExp ")" Block ElseIfStmt

syntax BExp ::= Bool
                    | AExp "<" AExp  [strict]
                    | AExp "<=" AExp [strict]
                    | AExp ">" AExp  [strict]
                    | AExp ">=" AExp [strict]
                    | AExp "==" AExp [strict]
                    | AExp "!=" Aexp [strict]
                    | "(" BExp ")"   [bracket]


syntax AExpMod ::= Id "++" 
                    | Id "--"


syntax AExp ::= Int
                | Id
                > left: AExp "*" AExp [seqstrict]
                > left: AExp "/" AExp [seqstrict]
                | AExp "-" AExp [seqstrict]
                | AExp "+" AExp [seqstrict]
                | "(" AExp ")"  [bracket]

syntax Type ::= "int" | "bool" | "string"

syntax Ids ::= List{Id, ","}

syntax ListValues ::= List{Int, ","}
                        |List{Bool, ","}
                        |List{String, ","}

syntax ArrayList ::= "{"ListValues"}" 

syntax DecVar ::= "var" Ids //para depois atribuição

syntax DecVar1 ::= "var" Id Type // para default

syntax UniqueIdAssigner ::= Id "=" AExp[strict(2)]

syntax Assigner::= |DecVar "=" AExp[strict(2)]
                        |DecVar "=" BExp[strict(2)]
                        |DecVar "=" SExp[strict(2)]
                        |UniqueIdAssigner
                        |Id "=" BExp [strict(2)]
                        |Id "=" SExp [strict(2)]
                        |Ids ":=" AExp[strict(2)] /*dec/assigner inferencia go*/
                        |Ids ":=" BExp[strict(2)]
                        |Ids ":=" SExp[strict(2)]
                  
rule forp1 (B:BExp) { S:Stmt } => if(B){ S forp1 (B) { S } } [structural]

rule for(var I:Id = V:AExp ; B:BExp ; Amod:AExpMod) {S} => I=V ~> forp1 (B) { S Amod } [structural]

    rule I1:Int + I2:Int => I1 +Int I2
    rule I1:Int - I2:Int => I1 -Int I2
    rule I1:Int * I2:Int => I1 *Int I2
    rule I1:Int / I2:Int => I1 /Int I2
    rule I1:Int < I2:Int => I1 <Int I2
    rule I1:Int <= I2:Int => I1 <=Int I2
    rule I1:Int > I2:Int => I1 >Int I2
    rule I1:Int == I2:Int => I1 ==Int I2
    rule I1:Int != I2:Int => I1 !=Int I2
        //rule I1:Id + I2 => I1 ~> I1 + I2
    //rule I:Int ~> I1:Id + I2 => I + I2
    //rule I1:Int + I2:Id => I2 ~> I1 + I2

        rule if (true) {S:Stmt} => S
        rule if (false) {_} => Skip
        rule if (false) {B} S:ElseIfStmt => B
        rule if (false) {_} S:ElseifStmt => S
        rule else if  (B:BExp) {S1:Stmt} S2:ElseifStmt => if (B) {S1} S2
        rule else if (B:BExp) {S:stmt} => if (B) {S}
        rule else {S} => S

        //regras inferencia de tipo
        rule I:Id := V:Int  
        rule I:Id := V:Bool
        rule I:Id := V:String


        rule Skip => .
// executar o programa
        rule func main () {B:Block} => B [structural]
// dec mais de uma variavel
        rule S1:Stmt S2:Block => S1 ~> S2

// decvar default INT
        rule <K> var I:Id T:Type  => Skip ... </K>
        <env> Env:Map => Env I |-> L </env>
        <store>Store:Map Store L |-> 0 </store>
         <loc> L:Int => L +Int 1 </loc>
//default list
         rule <K> var (I:Id, Xs:Ids) T:Type  => Xs T ... </K>
        <env> Env:Map => Env I |-> L </env>
        <store>Store:Map Store L |-> 0 </store>
         <loc> L:Int => L +Int 1 </loc> 
         // list skip default
         rule .Ids T:Type => Skip

 // assigner int/bool
        rule <K> var I:Id = V:Int => Skip ... </K>
        <env> Env:Map => Env I |-> L </env>
        <store>Store:Map Store L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
//list int
        rule <K> var (I:Id, Xs:Ids) = V:Int => Xs = V ... </K>
        <env> Env:Map => Env I |-> L </env>
        <store>Store:Map Store L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
//bool 
        rule <K> var I:Id = V:Bool => Skip ... </K>
        <env> Env:Map => Env I |-> L </env>
        <store>Store:Map Store L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
//bool list
        rule <K> var (I:Id, Xs:Ids) = V:Bool => Xs = V ... </K>
        <env> Env:Map => Env I |-> L </env>
        <store>Store:Map Store L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
//skip list assigner(acredito que tbm serve para inferencia testar depois)
rule .Ids = _:Int => Skip
rule .Ids = _:Bool => Skip

// assigner int/bool com inferencia
        rule <K> I:Id := V:Int => Skip ... </K>
        <env> Env:Map => Env I |-> L </env>
        <store>Store:Map Store L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
//int list
        rule <K> (I:Id, Xs:Ids) := V:Int => Xs = V ... </K>
        <env> Env:Map => Env I |-> L </env>
        <store>Store:Map Store L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
//bool
        rule <K> I:Id := V:Bool => Skip ... </K>
        <env> Env:Map => Env I |-> L </env>
        <store>Store:Map Store L |-> v </store>
        <loc> L:Int => L +Int 1 </loc>
//bool list
        rule <K> (I:Id, Xs:Ids := V:Bool => Xs = V ... </K>
        <env> Env:Map => Env I |-> L </env>
        <store>Store:Map Store L |-> v </store>
        <loc> L:Int => L +Int 1 </loc>

//dps da declaração fazer uma atribuição
        rule <K> I:Id = V:Int => Skip ... </K>
            <env> ... I |-> L ... </env>
            <store> ... L |-> (_ =>V) ... </store>
// qnd for um id
            rule <K> I1:Id = I2:Id => I1: = V ... </K>
            <env> ... I2 |-> L ... </env>
            <store> ... L |-> (_ =>V) ... </store>

//regra para encontrar o valor de um Id (ex count)
             rule <K> I:Id => V: ... </K>
            <env> ... I |-> L ... </env>
            <store> ... L |-> v ... </store>

//++ && --
            rule <K> I:Id ++ => Skip ... </K>
            <env> ... I |-> L ... </env>
            <store> ... L |-> (v =>V +Int 1) ... </store>

            rule <K> I:Id -- => Skip ... </K>
            <env> ... I |-> L ... </env>
            <store> ... L |-> (v =>V -Int 1) ... </store>

            


//começo programa
        configuration <T> 
        <K>$PGM:Pgm</K>
        <env> .Map </env>
        <store>.Map</store>
         <loc> 1 </loc>
        </T>

        endmodule

        module GO

        import DOMAINS
        import GO-SYNTAX

        syntax KResult ::= Int | Bool

        endmodule