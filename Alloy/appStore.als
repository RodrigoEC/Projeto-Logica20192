module appStore

//DÚVIDAS
//01) Usuário pode ter mais de uma conta mesmo?
//R1) Acho que não, um usuario só tem 1 conta, se tiver 2 contas são 2 usuarios

//02) Um dispositivo pode ter apps se não estiver associado à nenhum usuário?
//R2) Se um dispositivo tem um app ele tem que obrigatoriamente estar associado a um usuario.

//03) Onde vai ficar o status do app?
//R3) Acho q pode ficar dentro do app msm, a gente pode fazer um fact em que não existe app desinstalado
//    em um device.

//04) Haverão dois métodos (installApps e associateApp)? Pq um incrementa o objeto no set, e o outro atualizaria o status apenas.
//R4) Acho interessante que quando um app for instalado ele ja fazer o que o associate faz

//05) Como será a recebeção da nova versão do app? Um novo objeto do tipo App com a versão diferente?
//R5) Acho que mudar apenas a versão seria legal.                                                                              Uma atualização direta da versão no objeto?


//---------------SIGNATURES---------------

sig Usuario {
	devices: some Device, // todo usuario tem pelo menos 1 device, se não ele teria conta
	credit: Int, // o credito não pode ser menor que 0
	associatedApps: set App // Qualquer app pode vir estar aqui (installed ou uninstalled)
}


sig Device {
	memory: Int, //A memoria não pode ser negativa
	apps: set App // Os devices podem ter 0 apps
			 // Todos app em um device tem o status "installed"
			 // Não existem nenhum app que está no device e não está nos associatedApps.
}

sig App {
	size: Int, // O size tem q ser maior que 0
	version:  Version, // Eh isso
	price: Int, // O price não pode ser menor que 0
	status: one Status // (installed ou uninstalled)
}

sig Version{}

abstract sig Status {}
sig installed extends Status{}
sig uninstalled extends Status{}



//---------------FACTS---------------

fact {

--	all disj u1,u2:Usuario | !(some c:Conta |(c in u1.contas and c in u2.contas)) //Contas únicas, por usuário
	all u: Usuario | u.credit >= 0 // O crédito de um usuario é sempre maiour ou igual a 0
	all s: Status | one status.s // todo objeto sstatus está associado a um app
	all d:Device | one devices.d // todo device pertence a um usuario
	all a: App | (one apps.a) => (one associatedApps.a) // todo app que está instalado em um device está nos associados tbm
	all a: App | (not one apps.a) => (a.status = installed)
	
	
	//Coisas que podem ser penetrada aqui (ou não):
	//-um dispositivo tem apps se ele está associado à um usuário
	//-Um app pode estar em vários dispositivos
}




//---------------PREDICADOS---------------



//Instala aplicativo
pred installApp[a:App, u:Usuario, d:Device]{
	(minus[getCredit[u], getPrice[a]] >= 0 && minus[getMemory[d], getSize[a]] >= 0) => (associateApp[a, u, d] && d in (u.devices) && a in (d.apps) && a.status = installed )
}



//Associa aplicativo
pred associateApp[a:App, u:Usuario, d:Device]{
	

	d in (u.devices) //dispositivo pertence ao usuario

	a !in (d.apps) //app não está nos apps do dispositivo


	a.status = installed
	d.apps = d.apps + a
}



//Remove aplicativo
pred removeApp[a:App, u:Usuario, d:Device]{
	d in (u.devices)  //dispositivo pertence ao usuario
	a not in (d.apps)
	
	a.status = uninstalled
}

//Atualiza aplicativo
pred updateApp[a:App, u:Usuario]{
	
}


//---------------FUNÇÕES---------------
fun getAssociatedApps[u:Usuario]: set App{
	u.associatedApps
}

fun getStatus[a:App]: one Status {
	a.status
}

fun getCredit[u:Usuario]: one Int {
	u.credit
}

fun getSize[a:App]: one Int {
	a.size
}

fun getPrice[a:App]: one Int {
	a.price
}

fun getMemory[d: Device]: one Int {
	d.memory
}




pred show[] {
}
run show for 2
