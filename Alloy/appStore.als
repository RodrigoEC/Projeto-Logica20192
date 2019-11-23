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
	all d: Device, a: App| (appInDevice[a, d]) => minus[getMemory[d], sum(d.apps.size)] > 0
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

-----------------ASSERT-----------------

assert appStore {
	all u:User | one ap:appStore | (u in ap.usuarios)
	all a:App|  one ap:appStore | (a in ap.allApps)
}

assert User {
	all d: Device | one u: User | d in u.devices
	all u: User | getCredit[u] >= 0
}

assert Device {
	all d: Device  | (minus[getMemory[d], sum(d.apps.size)] <= 0)
}









pred show[] {}
run show for 10 Int


check appStore for 5 
check User for 500

check Device for 30
