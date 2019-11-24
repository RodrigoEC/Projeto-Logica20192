module appStore

//DÚVIDAS
//01) Usuário pode ter mais de uma conta mesmo? (CHECK)
//R1) Acho que não, um usuario só tem 1 conta, se tiver 2 contas são 2 usuarios

//02) Um dispositivo pode ter apps se não estiver associado à nenhum usuário? (CHECK)
//R2) Se um dispositivo tem um app ele tem que obrigatoriamente estar associado a um usuario.

//03) Onde vai ficar o status do app? (CHECK)
//R3) Acho q pode ficar dentro do app msm, a gente pode fazer um fact em que não existe app desinstalado
//    em um device.

//04) Haverão dois métodos (installApps e associateApp)? 
// Pq um incrementa o objeto no set, e o outro atualizaria o status apenas.
//R4) Acho interessante que quando um app for instalado ele ja fazer o que o associate faz

//05) Como será a recebeção da nova versão do app? Um novo objeto do tipo App com a versão diferente?
//R5) Acho que mudar apenas a versão seria legal.                                                                              Uma atualização direta da versão no objeto?


//---------------SIGNATURES---------------

one sig appStore {
	usuarios: some User,
	allApps: set App
}

sig User {
	devices: some Device, // todo usuario tem pelo menos 1 device, se não ele teria conta
	credit: one Int, // o credito não pode ser menor que 0
	associatedApps: set App // Qualquer app pode vir estar aqui (installed ou uninstalled)
}


sig Device {

	memory: one Int, //A memoria não pode ser negativa
	apps: set App // Os devices podem ter 0 apps
			 // Todos app em um device tem o status "installed"
			 // Não existem nenhum app que está no device e não está nos associatedApps.
}

sig App {
	size: one Int, // O size tem q ser maior que 0
	version: one Version, // Eh isso
	price: Int, // O price não pode ser menor que 0
	status: one Status // (installed ou uninstalled)

	// Um app poderia ter  "some " versions, aí ele teria a versão atual
}

sig Version{}

abstract sig Status {}
one sig installed extends Status{}
one sig uninstalled extends Status{}



-----------------FACTS------------------
fact insideAppStore{
	all u: User, ap:appStore | userInAppStore[u, ap]
	all a: App, ap:appStore | appInAppStore[a, ap]
}

fact insideUser {
	all d: Device | one u: User | deviceInUser[d, u]
	all u: User | getCredit[u] >= 0
	all u: User, d: Device, a: App | (deviceInUser[d, u] && appInDevice[a, d]) => (appInAssociation[a, u])
}

fact insideDevice {
	all d: Device | getMemory[d] > 0
	all d: Device, a: App | (appInDevice[a, d]) => (a.getStatus = installed)
	all d: Device, a: App| (appInDevice[a, d]) => (minus[getMemory[d], plus[getSize[a], getSize[a]]] >= 0) //Nao to conseguindo pensar de em um jeito pra fazer isso dar certo de vdd

}

fact insideApp {
	all a: App | some d:Device | (getStatus[a] = installed) => (appInDevice[a, d]) 
	all a: App | getPrice[a] >= 0
	all a: App | getSize[a] > 0
}

fact insidestatus {
	all s: Status | some status.s

}



-----------------PRED-------------------


pred deviceInUser[d:Device, u: User] {
	d in u.devices
}

pred userInAppStore[u: User, ap: appStore] {
	u in ap.usuarios
}

pred appInAppStore[a:App, ap:appStore] {
	a in ap.allApps
}

pred appInDevice[a: App, d: Device] {
	a in d.apps
}

pred appInAssociation[a: App, u: User] {
	a in u.associatedApps
}



-----------------FUN--------------------

fun getCredit[u: User]: one Int{
	u.credit
}

fun getMemory[d: Device]: one Int {
	d.memory
}

fun getStatus[a: App]: one Status {
	a.status
}

fun getSize[a: App]: one Int {
	a.size
}

fun getPrice[a: App]: one Int {
	a.price
}

-----------------ASSERT-----------------

assert appStore {
	all u:User | one ap:appStore | (u in ap.usuarios)
	all a:App|  one ap:appStore | (a in ap.allApps)
}

assert User {
	all d: Device | one u: User | d in u.devices
	all u: User | getCredit[u] >= 0
}


assert App {
	all a: App | a.price >= 0
	// Falta fazer com que a soma dos preços dos apps não ultrapasse o valor dos creditos do usuario
}

// Falta fazer a parte de como atualizar um app 





pred show[] {}
run show for 10 Int


check appStore for 5 
check User for 500

check App for 5 Int

