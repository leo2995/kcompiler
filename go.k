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
                | FuncCall
                | Assigner
                | AExpMod
                | Skip
                | Stmt Stmt [left]

syntax Values ::= List{Int, ","}
syntax Params ::= List{Id, ","}
syntax FuncDec ::= "func" Id "(" Params ")" Block
syntax FuncCall ::= Id "(" Values ")"
syntax Local ::= "local" "("Id "," Stmt ")"

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

syntax SExp ::= String
                |SExp "+" SExp {seqstrict. left}
                |Id

rule S1:String + S2:String S1 => S1 +String S2


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
        rule S1:Stmt S2:Stmt => S1 ~> S2
//dentro de uma funcao
        rule local(I:Id, S1:Stmt S2:Stmt) => local(I, S1) ~> local(I, S2)

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

//instanciando celulas da configuração/ salvar id e escopo /funcao/declaracao
            rule <k> func I:Id (P:Params) { S:Stmt } => Skip ... </k>
            (.Bag => <thread>
                <Id> I </Id>
                <scope> S </scope>
                <params> P </params>
                <temp> P </temp>
                <localEnv> .Map </localEnv>
                 </thread>
            
            )
                <functions> M:Map => M I |-> S </functions>

//resolvendo a funcao variaveis locais/ chamada da funcao e seu escopo/chamada
        rule <k> I:Id (.Values)  => local(I, S) ... </k>
        <thread>
        ...
        <Id> I </Id>
        <scope> S:Stmt </scope>
        <params> P </params>
         <temp> (.Params =>P) </temp>
        ...
        </thread>

        rule <k> I:Id ((V:Int,Vs:Values))  => I:Id (Vs) ... </k>
        <thread>
        ...
        <Id> I </Id>
        <temp> (P:Id, Ps:params => Ps) </temp>
        <localEnv> M:Map => M P |-> L </localEnv>
        ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>

//replicar para bool e string / resolvendo a parte de local e global
        rule <k> local(FuncId:Id, var I:Id = V:Int)  => Skip ... </k>
             rule <k> I:Id ()  => local(I, S) ... </k>
        <thread>
        ...
        <Id> FuncId </Id>
        <localEnv> M:Map => M I |-> L </localEnv>
        ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>


            


//começo programa
        configuration <T> 
        <K>$PGM:Pgm</K>
       <functions color="orange">
        <thread multiplicity="*" color="blue"> 
        <Id> .K </Id>
        <scope> .K </scope>
        <params> .K </params>
        <temp> .K </temp>
        <localEnv> .Map </localEnv>
        </thread>
        </functions>
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