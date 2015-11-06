// for Boolean type
open util/boolean 

sig Strings{}

// date and time for requests
sig DateTime {
	day: one Int,
	month: one Int,
	year: one Int,
	hour: one Int,
	minute: one Int
}

// location for requests
sig Location {
	address: one Strings,
	city: one Strings,
	zipCode: one Int
}

// base user data
abstract sig RegisteredUser {
	id: one Int,
	email: one Strings,
	telephoneNumber: one Int
}

// passenger
sig Passenger extends RegisteredUser {
	currentRequest: lone Request
}

// driver
sig Driver extends RegisteredUser {
	busy: one Bool,
	currentRequest: lone Request,
	maxPassengers: one Int
}

// call center operator
sig CallCenterOperator extends RegisteredUser { }

// request
sig Request {
	id: one Int,
	fromCall: one Bool,
	assignedOperator: lone CallCenterOperator,
	passenger: one Passenger,
	driver:  lone Driver,
	location: one Location,
	ended: one Bool,
	numberOfPassengers: one Int,
	date: one DateTime
}

// queue
sig Queue {
	id: one Int,
	drivers: set Driver,
	area: one Area
}

// area
sig Area {
	id: one Int,
	queue: one Queue
}

// ID must be unique between users
fact noDuplicateUserId {
	no disj u1, u2: RegisteredUser | u1.id = u2.id
}

// ID must be unique between users, independently from their type
fact noDuplicateRoles {
	no p: Passenger, d: Driver, c: CallCenterOperator | p.id = d.id or p.id = c.id or d.id = c.id
}

// Email and phone number must be unique
fact noDuplicateUserData {
	no disj u1, u2: RegisteredUser | (u1.email = u2.email) or (u1.telephoneNumber = u2.telephoneNumber)
}

// Each request ID must be unique
fact noDuplicateRequestId {
	no disj r1, r2: Request | r1.id = r2.id
}

// Each request must be unique
fact noDuplicateRequest {
	no disj r1, r2: Request | (r1.passenger = r2.passenger) and (r1.driver = r2.driver) and (r1.date = r2.date) and (r1.location = r2.location) and (r1.ended = False or r2.ended = False)
}

// Each queue ID must be unique
fact noDuplicateQueueId {
	no disj q1, q2: Queue | q1.id = q2.id
}

// Each area ID must be unique
fact noDuplicateAreaId {
	no disj a1, a2: Area | a1.id = a2.id
}

// Each area can have only one queue
fact noDuplicateAreaInQueueu {
	no disj q1, q2: Queue | q1.area = q2.area
}

// Each queue can have only one area
fact noDuplicateQueueInArea {
	no disj a1, a2: Area | a1.queue = a2.queue
}

// If a request is made through a telephone call, it must be insterted by an operator
fact requestMadeByCallHasOperator {
	all r: Request | (r.fromCall = True) => (one c: CallCenterOperator | r.assignedOperator = c)
}

// If a driver is not busy, must be in a queue
// AND
// If a driver is in a queue, must be not busy
fact driverNotBusyIsInAQueueAndViceVersa {
	all d: Driver | one q: Queue | (d.busy = False) <=> (d in q.drivers)
}

// If a driver is busy, must not be in a queue
// AND
// If a driver is not in a queue, must be busy
fact driverBusyNotInQueueAndViceVersa {
	all d: Driver | d.busy = True <=> (no q: Queue | d in q.drivers)
}

// Each taxi can be in only one queue max
fact noDuplicateTaxiInQueue {
	all disj q1, q2: Queue, d: Driver | (d in q1.drivers) <=> (d not in q2.drivers)
}

// Each passenger can have only one active simultaneous request
fact noMultipleActiveRequestForPassenger {
	no disj r1, r2: Request | r1.passenger = r2.passenger and r1.ended = False and r2.ended = False
}

// If a request is not ended, its driver is busy
fact requestNotEndedImpliesDriverBusy {
	all r: Request | (r.ended = False) => (r.driver.busy = True) 
}

// Each driver can have max one active request
fact oneDriverPerActiveRequest {
	no disj r1, r2: Request | r1.driver = r2.driver and r1.ended = False and r1.ended = False
}

// Each driver that have an active request is busy
fact driverInNotEndedRequestIsBusy {
	all d: Driver, r: Request | (r.driver = d and r.ended = False) => d.busy = True
}

// Check that no passenger can have more than one active request
assert noMultipleRequestActiveForPassenger {
	no disj r1, r2: Request | r1.ended = False and r2.ended = False and r1.passenger = r2.passenger
}
check noMultipleRequestActiveForPassenger

// Check that no driver can be assigned to more than one active request
assert noMultipleRequestActiveForDriver {
	all d: Driver | all disj r1, r2: Request | (r1.driver = d and r2.driver = d) => (r1.ended = True or r2.ended = True)
}
check noMultipleRequestActiveForDriver

// Check that each driver can be at maximum in a queue
assert driverInMaxOneQueue {
	all d: Driver | all disj q1, q2: Queue|  not( (d in q1.drivers) and (d in q2.drivers) ) 
}
check driverInMaxOneQueue

// Check that all drivers in a queue are not busy
assert noDriverInQueueAndBusy {
	all d: Driver | all q: Queue | (d.busy = True) => (d not in q.drivers)
}
check noDriverInQueueAndBusy

// Check that all drivers not busy are in a queue
assert driverNotBusyIsInAQueue {
	all d: Driver | d.busy = False => (one q: Queue | d in q.drivers)
}
check driverNotBusyIsInAQueue

// Check that all drivers assigned to a request not ended, are busy
assert driverInRequestNotEndedIsBusy {
	all r: Request | r.ended = False => r.driver.busy = True
}
check driverInRequestNotEndedIsBusy

// Check that all request made using a telephone call has an operator assigned
assert requestMadeByCallHasAnOperator {
	all r: Request | r.fromCall = True => (one c: CallCenterOperator | r.assignedOperator = c)
}
check requestMadeByCallHasAnOperator

// Support function that adds a driver to a queue
pred addDriverToQueue [q1, q2: Queue, d: Driver] {
	q2.drivers = q1.drivers + d
}
run addDriverToQueue

// Support function that removes a driver from a queue
pred removeDriverFromQueue[q1, q2: Queue, d: Driver] {
	q2.drivers = q1.drivers - d
}
run removeDriverFromQueue

// Support function that assigns a request to a driver
pred addDriverToRequest[r: Request, d: Driver] {
	r.driver = d
}
run addDriverToRequest

// Check that adding a driver to a queue and removing he/she, the queue ramins not changed
assert addDriverToQueueUndoesRemoveDriverFromQueue {
	all q1, q2, q3: Queue, d: Driver | (d in q1.drivers and removeDriverFromQueue[q1, q2, d] and addDriverToQueue[q2, q3, d] ) => q1.drivers = q3.drivers
}
check addDriverToQueueUndoesRemoveDriverFromQueue

// Check that removing a driver from a queue and adding he/she, the queue ramins not changed
assert removeDriverFromQueueUndoesAddDriverToQueue {
	all q1, q2, q3: Queue, d: Driver | (d not in q1.drivers and addDriverToQueue[q1, q2, d] and removeDriverFromQueue[q2, q3, d] ) => q1.drivers = q3.drivers
}
check removeDriverFromQueueUndoesAddDriverToQueue

// Check if addDriverToQueue works
assert addDriverToQueueIsWorking {
	all d: Driver, q1, q2: Queue | ( (d not in q1.drivers) and d.busy = False and addDriverToQueue[q1, q2, d]) => (d in q2.drivers)
}
check addDriverToQueueIsWorking

// Check if removeDriverFromQueue works
assert removeDriverFromQueueIsWorking {
	all d: Driver, q1, q2: Queue | (d in q1.drivers and removeDriverFromQueue[q1, q2, d]) => (d not in q2.drivers)
}
check removeDriverFromQueueIsWorking

// Check if addDriverToRequest works
assert addDriverToRequestIsWorking {
	all r: Request, d: Driver | (r.driver = none and d.busy = False and (one q: Queue | d in q.drivers) and addDriverToRequest[r, d]) => (r.driver = d and (no q: Queue | d in q.drivers) and d.busy = True)
}
check addDriverToRequestIsWorking

// Show a world with some requests not ended
pred showRequest {
	some r: Request, d: Driver, p: Passenger | r.driver = d and r.passenger = p and d.busy = True and r.ended = False
}
run showRequest for 5

// Show a world with drivers available or busy with a request assigned
pred showDrivers {
	some d: Driver | d.busy = False => (no r: Request | r.driver = d)
}
run showDrivers for 5

// Show a world with request made from telephone with an operator assigned
pred showRequestFromCallCenter {
	some r: Request, c: CallCenterOperator | r.fromCall = True and r.assignedOperator = c
}
run showRequestFromCallCenter for 5

// Show a world with drivers in a queue
pred showQueue {
	some d: Driver, q: Queue | d.busy = False => d in q.drivers
}
run showQueue for 5

// Show a world with a certain number of components
pred show {
	#Area = #Queue
	#Area > 0
	#Driver > 0
	#Passenger > 0
	#Request > 0
}
run show for 5
