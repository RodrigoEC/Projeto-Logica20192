module appStore


//---------------SIGNATURES---------------

one sig appStore {
	-- Conjunto de usuarios do sistema.
	usuarios: some User,

	-- Conjunto de apps da appStore disponíveis para baixar.
	allApps: set App
}

sig User {
	-- Conjunto de devices de um usuario, sempre maior ou igual a 1.
	devices: some Device, 

	-- Credito que o usuario tem para comprar novos apps que ja não foram instalados.
	creditAvailable: one Int,

	-- Apps que foram instalados ou que estão instalados em algum device do usuario.
	associatedApps: set App
}


sig Device {

	-- Memoria disponível em um device. Ele não conta a memoria dos apps, ja que ela ja foi 
	--"consumida" pelos apps instalados.
	memoryAvailable: one Int,

	-- Conjunto de apps instalados nesse device
	apps: set App
			 // Não existem nenhum app que está no device e não está nos associatedApps.
}

sig App {
	-- Espaço que o app ocupa no device que ele esta instalado ou no qual ele vai estar instalado.
	size: one Int,

	-- Versão atual do app.
	version: one Version,

	-- Preço do app.
	price: Int,

	-- Status de um app na conta do usuario. Se um app está instalado em algum dos dispositivos do 
	--Usuario então ele tem o status "installed"
	status: one Status 
}

-- Versão de algum app.
sig Version{}

abstract sig Status {}
one sig installed extends Status{}
one sig uninstalled extends Status{}



-----------------FACTS------------------
fact insideAppStore{
	-- Todos os users estão dentro da appStore.
	all u: User, ap:appStore | userInAppStore[u, ap]

	-- Todos os apps, instalados ou não estão cadastrados na appStore.
	all a: App, ap:appStore | appInAppStore[a, ap]
}

fact insideUser {
	-- Todo device pertence a exatamente 1 usuario.
	all d: Device | one u: User | deviceInUser[d, u]

	-- A quantidade de crédito de um user sempre eh maior ou igual a 0.
	all u: User | getCreditAvailable[u] >= 0

	-- Se um app "A" está dentro de um dispositivo "D" e esse dispositivo pertence a um user "U"
	--Então "A" está nos apps associados de "U".
	all u: User, d: Device, a: App | (deviceInUser[d, u] && appInDevice[a, d]) => (appInAssociation[a, u])
}

fact insideDevice {
	--A memória de um device não pode ser menor do que 0
	all d: Device | getMemoryAvailable[d] >= 0

	--Todos os apps em um device tem o status "installed"
	all d: Device, a: App | (appInDevice[a, d]) => (getStatus[a] = installed)
}

fact insideApp {
	-- Se o status de um app eh "installed" então existe pelo menos 1 dispositivo em que ele está instalado.
	all a: App | some d:Device | (getStatus[a] = installed) => (appInDevice[a, d]) 

	-- O preço de um app nunca é menor que 0.
	all a: App | getPrice[a] >= 0

	-- A memória que um app ocupa em um device é sempre maior que 0.
	all a: App | getSize[a] > 0

	-- Apps diferentes tem versões diferentes.
	all disj a1, a2 : App | getVersion[a1] != getVersion[a2]
}


fact insidestatus {
	-- Todo status está relacionado a algum app. Não existe a entidade status por sí só.
	all s: Status | some a: App | getStatus[a] = s

}



-----------------PRED-------------------

-- O device passado como parametro está nos devices do user passado como parametro.
pred deviceInUser[d:Device, u: User] {
	d in u.devices
}

-- O user passado como parametro pertence ao conjunto de usuarios da appStore passada como parametro.
pred userInAppStore[u: User, ap: appStore] {
	u in ap.usuarios
}

-- O app passado como parametro pertence ao conjunto de apps da appStore passada como parametro.
pred appInAppStore[a:App, ap:appStore] {
	a in ap.allApps
}

-- O app passado como parametro pertence ao conjunto de apps do device passado como parametro.
pred appInDevice[a: App, d: Device] {
	a in d.apps
}

-- O app passado como parametro pertence ao conjunto de apps associados ao usuario passado como parametro.
pred appInAssociation[a: App, u: User] {
	a in u.associatedApps
}



-----------------FUN--------------------

-- Função que retorna os creditos disponíveis de um user.
fun getCreditAvailable[u: User]: one Int{
	u.creditAvailable
}

-- Função que retorna os espaço disponível em um device.
fun getMemoryAvailable[d: Device]: one Int {
	d.memoryAvailable
}

-- Função que retorna os status de um app, podendo ser "installed" ou "uninstalled"
fun getStatus[a: App]: one Status {
	a.status
}

-- Função que retorna o espaço que o app passado como parametro ocupa se for instalado.
fun getSize[a: App]: one Int {
	a.size
}

-- Função que retorna o preço do app passado como parametro.
fun getPrice[a: App]: one Int {
	a.price
}

-- Função que retorna a versão do app passado como parametro.
fun getVersion[a: App]: one Version {
	a.version
}

-----------------ASSERT-----------------

assert appStore {
	all u:User | one ap:appStore | (u in ap.usuarios)
	all a:App|  one ap:appStore | (a in ap.allApps)
}

assert User {
	all d: Device | one u: User | d in u.devices
	all u: User | getCreditAvailable[u] >= 0
}


assert App {
	all a: App | a.price >= 0
}






pred show[] {}
run show for 10 Int


check appStore for 5 
check User for 500

check App for 5 Int

