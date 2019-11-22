module appStore

//DÚVIDAS
//-Usuário pode ter mais de uma conta mesmo?
//-Um dispositivo pode ter apps se não estiver associado à nenhum usuário?
//-Onde vai ficar o status do app?
//-Usuário vai ter mesmo mais de uma conta?
//-Haverão dois métodos (installApps e associateApp)? Pq um incrementa o objeto no set, e o outro atualizaria o status apenas.
//-Como será a recebeção da nova versão do app? Um novo objeto do tipo App com a versão diferente?
//                                                                               Uma atualização direta da versão no objeto?


//---------------SIGNATURES---------------

sig Usuario {
	devices: set Device,
	contas: one Conta
}

sig Conta {
	credit: Int,
	associatedApps: set String
}

sig Device {
	memory: Int,
	apps: set App
}

sig App {
	name: String,
	size: Int, 
	version:  String,
	price: Int,
	status: String //penetrei isso aq só pra coisar
}

one sig Calc extends App{} {
	name = "calculadora"
	version = "1.05.2"
	size = 1
	price = 0
}

one sig Alarm extends App{} {
	name = "alarme"
	version = "2.02.2"
	size = 1
	price = 0
}

//---------------FACTS---------------

fact {

	all disj u1,u2:Usuario | !(some c:Conta |(c in u1.contas and c in u2.contas)) //Contas únicas, por usuário
	all c:Conta | one contas.c //quê?
	all c: Conta | c.credit >= 0
	
	//Coisas que podem ser penetrada aqui (ou não):
	//-um dispositivo tem apps se ele está associado à um usuário
	//-Um app pode estar em vários dispositivos
}


//---------------PREDICADOS---------------

//Instala aplicativo
pred installApp[a:App, u:Usuario, d:Device]{
	associateApp[a, u, d]
	
	d in (u.devices)  //dispositivo pertence ao usuario
	a.name in (appsConta[u]) //app está nos apps associados da conta do usuário
	a in (d.apps) //app está no dispositivo
	
	a.status = "installed"
}


//Associa aplicativo
pred associateApp[a:App, u:Usuario, d:Device]{
	d in (u.devices) //dispositivo pertence ao usuario
	a.name !in (appsConta[u]) //app não está nos apps da conta do usuário
	a !in (d.apps) //app não está nos apps do dispositivo

	appsConta[u] = appsConta[u] + a.name
	a.status = "installed"
	d.apps = d.apps + a
}



//Remove aplicativo
pred removeApp[a:App, u:Usuario, d:Device]{
	d in (u.devices)  //dispositivo pertence ao usuario
	a.name in (appsConta[u]) //app está nos apps associados da conta do usuário
	a in (d.apps)
	
	a.status = "uninstalled"
}

//Atualiza aplicativo
pred updateApp[a:App, u:Usuario]{
	
}


//---------------FUNÇÕES---------------
fun appsConta[u:Usuario]: set String{
	u.contas.associatedApps
}

pred show[] {
}
run show for 2
