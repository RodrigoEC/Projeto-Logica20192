module appStore

// SIGNATURES

sig Usuario {
	devices: set Device,
	contas: one Conta
}

sig Conta {
	credit: Int,
	associations: set String
}

sig Device {
	memory: Int,
	apps: set App
}

sig App {
	name: String,
	size: Int, 
	version: String,
	price: Int
}

one sig Calc extends App{} {
	name = "calculadora"
	version = "1.05.2"
}



// FACTS

fact {

	all disj u1,u2:Usuario | !(some c:Conta |(c in u1.contas and c in u2.contas))
	all c:Conta | one contas.c
	all c: Conta | c.credit >= 0


}


pred show[] {
}
run show for 3

