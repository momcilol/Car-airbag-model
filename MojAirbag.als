open util/ordering[Time] as T

sig Time {}

some sig Speed {
	value: Int
} {
	all v: value | v >= 0
}

-- ziroskop, sa vrednosti koju izmeri (promena gravitacione sile)
some sig Gyroscope {
	g_meter: Int
}
{
	all g: g_meter | g >= 0 and g <= 30
}

-- TODO: definisati kocnicu i ogranicenje da uvek vazi da jacina pritiska mora da bude izmedju 0 i 1 
-- (odnosno, predstaviti kao 0 -100)
-- nakon toga, dodati kocnicu na sva mesta gde je potrebno
some sig Brake {
    pressure: Int
}
{
    all p: pressure | p >= 0 and p <= 100
}

fact noDuplicates {
	all disj x, y: Speed | x.value != y.value
	all disj x, y: Gyroscope | x.g_meter != y.g_meter
	all disj x, y: Brake | x.pressure != y.pressure
}

abstract sig Sensor {
	signal: set Time
}

one sig ImpactSensor, SideSensor extends Sensor {}
some sig SeatWeightSensor, SeatbeltSensor extends Sensor {}

abstract sig Switch {
	on: set Time
}

abstract sig AirbagPosition {}
one sig Knee extends AirbagPosition {}
some sig Normal extends AirbagPosition {}

some sig AirbagSwitch extends Switch {}

one sig ACUSensors {
	speed: Speed one -> Time,
	gyro: Gyroscope one -> Time,
	frontal: ImpactSensor,
	side: SideSensor,
	brake: Brake one -> Time
}

some sig Airbag {
	on: set Time,
	activated: set Time, 
	seatbelt: SeatbeltSensor,
	weight: SeatWeightSensor,
	switch: AirbagSwitch, 
	sensors: ACUSensors,
	position: AirbagPosition
}

fact AirbagConstraint {
	all disj x, y : Airbag | 
		x.seatbelt != y.seatbelt
 		and x.weight != y.weight
		and x.switch != y.switch
		and x.position != y.position	
}


//	ADDITIONAL PREDICATES

pred is_on [a: Airbag, t: Time] {
	t in a.on and t in a.switch.on
}

pred are_conditions_ok[a: Airbag, t:Time] {
	t in a.switch.on and t in a.seatbelt.signal and t in a.weight.signal
}

pred is_activated[a: Airbag, t: Time] {
	t in a.activated
}

-- aktivacija jednog airbag-a
pred activate[a: Airbag, t, t": Time] {
	-- preconditions
	is_on[a, t] 
	are_conditions_ok[a, t]

	-- postcondition
	is_activated[a, t"]
	-- frame condition
//	activated_changes[Airbag - a, t, t"]
}

------TURN ON------

pred turn_on [a: Airbag, t, t": Time ] { 
	-- precondition: airbag is off
	!is_on[a, t]
	-- postcondition: airbag is on
	is_on[a, t"]
}

------TURN OFF-----

pred turn_off [a: Airbag, t, t": Time ] { 
	-- precondition: airbag is on
	is_on[a, t]
	-- postcondition: airbag is off
	!is_on[a, t"]
}

------STILL IMPACT------

pred still_impact [a: Airbag, t, t": Time] {
	-- precondition
	let acu = a.sensors | 
		acu.speed.t.value < 3 and
		(t in acu.frontal.signal or t in acu.side.signal) and
		acu.gyro.t.g_meter >= 2
			
	-- postcondition
	activate[a, t, t"]
}

------SPEED IMPACT------

-- TODO: udarac u slucaju vece brzine
pred speed_impact [a: Airbag, t, t": Time] {
	--precondition
	let acu = a.sensors | 
		acu.speed.t.value >= 3 and
		(t in acu.frontal.signal or t in acu.side.signal) and
		acu.gyro.t.g_meter > 3

	--postcondition
	activate[a, t, t"]
}

-- TODO 4: ne zaboraviti i proveru da noga nije jako pritisnuta na kocnici
pred speed_impact_knee [a: Airbag, t, t": Time] {
	-- TODO 1 (uskladiti ime promenljive)
	--precondition
	let brake = a.sensors.brake.t |
    		brake.pressure < 70
	
	--postcondition
	speed_impact [a, t, t"]
}



------DYNAMICS------

pred transition [t, t": Time] {
	all a: Airbag |
		turn_on [a,t,t"] or
		turn_off [a,t,t"] or
		still_impact [a, t, t"] or 
		(a.position in Knee implies
			speed_impact_knee [a, t, t"] else
			speed_impact [a, t, t"])
}

pred dynamicStart {
	all t: Time - last | 
		let t" = t.next |
			transition[t, t"]
}

------INITIALIZATION------

pred init [t:Time] {
	#Airbag = 3
	#Normal = sub[#Airbag, 1]
	#AirbagSwitch = #Airbag
	#SeatWeightSensor = #Airbag
	#SeatbeltSensor = #Airbag

	#Brake = #Time
	#Speed = #Time
	#Gyroscope = #Time

	all a: Airbag | !is_on[a, t] and !is_activated[a, t]

	dynamicStart
}

------IDEJATA NA PROFESORKA OVAJ SAFETY, JA SO OVEM IČ NEMAM NIŠTO------

pred safety_check {
	init [T/first]
	some t: Time | safe [t]
} 

pred safe [t: Time] {
	ACUSensors.gyro.t.g_meter = 0 
}

------POKRETANJE------

run safety_check for 8 but 8 int

------ASSERTIONS------


