open util/integer

//POWER ENJOY

one sig PowerEnjoy {
	cars: set Car, 
	rentals: set Rental,
	users: set User
} 
{
	#cars >= 0
	#users >= 0
	#rentals >= 0
}

fact allInPowerEnjoy{
	all car: Car | car in PowerEnjoy.cars
	all user: User | user in PowerEnjoy.users
	all rental: Rental |rental in PowerEnjoy.rentals
}

abstract sig User {
	position: one Position,
	id: one Int
} 
{
	id >= 0
}

fact differentUserId {
	no disjoint  u1, u2: User |  u1.id = u2.id
}

//OPERATORS

sig Operator extends User {}

//POSITIONS

sig Position {
	positionX: one Int,
	positionY: one Int
}

abstract sig Area {
	positions: set Position
} 
{
	#positions > 0
}

one sig SafeArea extends Area {}
one sig UnsafeArea extends Area {}

fact disjointAreas {

	all p: Position | {
		p in SafeArea.positions or
		p in UnsafeArea.positions
	}

	no p: Position | {
		p in SafeArea.positions and
		p in UnsafeArea.positions
	}

}

fact noDuplicatedPositions {

	no p1, p2: Position | {
		p1 != p2 and
		p1.positionX = p2.positionX and
		p1.positionY = p2.positionY
	}

}

//GRID STATIONS

sig GridStation {
	position: one Position
}

fact allStationInSafeArea {
	all g: GridStation | g.position in SafeArea.positions
}

//CARS

sig Car {
	id: one Int,
	state: one CarState,
	position: one Position,
	battery: one BatteryState
}
{
	id >= 0
}

fact differentCarId{
	no disjoint  c1, c2: Car |  c1.id = c2.id
}

fact differentPositionForCars {
	no disjoint c1, c2: Car | c1.position = c2.position
}

abstract sig BatteryState {}
one sig BatteryLow extends BatteryState {}
one sig BatteryHigh extends BatteryState {}

abstract sig CarState {}
one sig Available extends CarState {}
one sig InUse extends CarState {}
one sig EmptyBattery extends CarState {}
one sig OrdinaryMaintenance extends CarState {}
one sig ExtraordinaryMaintenance extends CarState {}

fact batteryAndCarStateCoherence{
	all c: Car | (c.state = EmptyBattery) => (c.battery = BatteryLow) 
}

fact availableCarInSafeArea {
	all c: Car | (c.state = Available) => (c.position in SafeArea.positions) 
}

fact allCarsNotInSafeArea {
	all c: Car | (c.position in UnsafeArea.positions) => (c.state != Available) 
}

//CLIENTS

sig Client extends User {
	state: one ClientState,
}

abstract sig ClientState {}
one sig ActiveClient extends ClientState {}
one sig InactiveClient extends ClientState {} 

//RENTAL
abstract sig RentalPhase {
	time: one Int
}
{
	time >= 0
}

sig Reservation extends RentalPhase {
}
{
	time <= 60
}

sig Ride extends RentalPhase {
	passengers: one Passengers
}

sig Ended extends RentalPhase {
}

abstract sig Passengers {} 
one sig NoPassengers extends Passengers {}
one sig EnoughForDiscount extends Passengers {} 
one sig NotEnoughForDiscount extends Passengers {}

abstract sig Boolean {}
one sig True extends Boolean {}
one sig False extends Boolean {}

abstract sig Rental {
	id: one Int,
	user: one User,
	car: one Car,
	phase: one RentalPhase,
	fare: one Boolean 
}
{
	id >= 0
}

fact differentIdForeachRental {
	all pe: PowerEnjoy {
		all disjoint r1, r2: Rental | ((r1 in pe.rentals) and (r2 in pe.rentals)) => (r1.id != r2.id)
	}	
}

fact differentCarUserForeachActiveRental {
	all r1, r2: Rental | 
		(	
			(r1 != r2)
			and
			(r1.phase != Ended)
			and
			(r2.phase != Ended)
		)
		 <=>
		(r1.car != r2.car and r1.user != r2.user)
}

fact onlyClientsPay {
	all r: Rental | (r.user in Operator) => (r.fare = False)
	all r: Rental | (r.user in Client) => (r.fare = True)
}	

fact allRentCarAreInUse {
	all r: Rental | (r.phase != Ended) => r.car.state = InUse
}

fact inUseCarAreAllRent {
	no c: Car | {
		c.state = InUse 
		all r: Rental {
			c != r.car
		}
	}
}

fact inactiveClientCannotRent { 
	all c: Client, r: Rental | (r.user = c and r.phase != Ended) => (c.state = ActiveClient)
}

fact ifCarIsNotInSafeAreaRentalIsInRidePhase {
	all r: Rental, c: Car | 
		(r.car = c and (r.car.position in UnsafeArea.positions) ) 
		=>
		(r.phase = Ride)
	all  c: Car | 
		(c.position in UnsafeArea.positions ) 
		=>
		(c.state = InUse or c.state = ExtraordinaryMaintenance  )
}

fact userCarSamePositionOnRide {
	all rental: Rental | (rental.phase = Ride and (rental.car.position in SafeArea.positions) ) => (rental.user.position = rental.car.position)
}

//ASSERT

assert noCarWithTwoActiveRental {
	all c: Car, r: Rental |
		(r.car = c and r.phase != Ended) => {
			no r2: Rental | r != r2 and r2.phase != Ended and r2.car = c
		}
}
check noCarWithTwoActiveRental for 10

assert noUserWithTwoActiveRental {
	all c: Client, r: Rental |
		(r.user= c and r.phase != Ended) => {
			no r2: Rental | r != r2 and r2.phase != Ended and r2.user = c
		}
}
check noUserWithTwoActiveRental for 10

pred show{
	some Operator
	some GridStation 
	some r: Rental | r.phase = Reservation
	some r: Rental | r.phase = Ride
	some r: Rental | r.phase = Ended
	some c: Client | c.state = ActiveClient
	some c: Client | c.state = InactiveClient
	some c: Car | c.state = Available
	some c: Car | c.state = InUse
	some c: Car | c.state = EmptyBattery
	some c: Car | c.state = OrdinaryMaintenance
	some c: Car | c.state = ExtraordinaryMaintenance
}
run show for 25 but 8 Int

pred smallShow{
	#GridStation = 1
	#Operator = 1
	#ActiveClient = 1
	#InactiveClient = 1
	#Car = 3
	one r: Rental | r.phase = Reservation
	one r: Rental | r.phase = Ride
	one r: Rental | r.phase = Ended
	#Position = 5
	some Operator
}
run smallShow for 10 but 8 Int
