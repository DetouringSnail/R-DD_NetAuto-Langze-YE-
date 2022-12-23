abstract sig Bool{}
one sig TRUE extends Bool{}
one sig FALSE extends Bool{}

--For positive numbers
sig Float{
left: one Int,
right: one Int
} {
left >= 0
right >= 0
}
--class socket
sig Socket{
availablesocket: one Int,
occupiedsocket: one Int,
energyremain: one Int,
sockettype: one String,
socketcost: one Float
}

--Class charging station
sig ChargingStation{
ID: one Int,
name: one String,
location: one String,
Energyremain: one Int,
cpo: one CPO,
ifavailable: one Bool,
specialoffer: one Float,
timeslots: set TimeSlot,
sockets: set Socket
}{
Energyremain>=0
}


--class reservation order
sig Point{
ts:one Int
}{ts>0}
sig TimeSlot{
start: one Point,
end: one Point
}
sig Book{
ID: one Int,
havedone: one Bool ,
chargingslot: one TimeSlot,
}
sig Order{
number: one Int,
amount: one Float,
book: one Book,
createtime: one Point
}
sig ChargingOrder extends Order{
buyer: one Driver,
seller: one CPO
}




--new_user
sig Username{}
sig Email{}
sig Password{}
{
all p:Password | (some u: User| u.password=p)
}


--User: who use eMALL
abstract sig User{
username: one Username,
phone: Int,
email: one Email,
password: one Password
}
--Driver: driver using eMALL
sig Driver extends User{
drivername: one String,
carbatterystatus: one Float,
location: one String,
upcomingOrders: set ChargingOrder,
pastOrders: set ChargingOrder,
chargingbill: one Int,
carchargingstatus: one String
}
sig CPO extends User{
chargingstations: set ChargingStation,
chargingOrders: set ChargingOrder
}


sig eMSP{}


//Some facts
//Every username is associated with one and only one user
fact usernameBelongstoAUser{
all un: Username | one u:User | u.username=un
}


//Every email is associated with one and only one user
fact emailBelongstoAUser{
all em: Email | one u:User | u.email=em
}


//Every address is associated with only one charging station
fact addressonly{
all lt: String | one cs: ChargingStation | cs.location=lt
}

//Every CPO has at least one charging station
fact CPOhasatleastOneChargingStation{
all c: CPO | #(c.chargingstations)>0
}

//A charging station must have a CPO
fact chargingstationWithCPO{
all cs:ChargingStation | one c:CPO | cs.cpo=c
}

//Every charging station has at least one socket
fact ChargingStationHasatleastOneSocket{
all c:ChargingStation | (#c.sockets>0)
}




pred eMALL {
# User =2
# Driver = 1
# CPO = 1
# ChargingStation = 2
# ChargingOrder=1
some d : Driver | #( d. pastOrders ) > 0 and #(d.upcomingOrders)>0
some c : CPO    | # (c.chargingOrders)>0
}
run eMALL for 10

