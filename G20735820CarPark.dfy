//using autocontracts so that Valid predicate is added to pre and post conditions
class {:autocontracts} CarPark{
    const capacity : int := 10; //capacity of non-reserved car park
    const rCapacity : int := 10; //capacity of reserved car park
    const weekendCapacity : int := 20; //total cap of carpark as on weekend all spaces are available as non-reserved
    var urArea : set<int>; //non-reserved car park represented as a set so there are no duplicates
    var rArea : set<int>; // reserved car park also a set so no duplicates
    var subs: set<int>; //set to hold the car id when making reservation 
    const fullSpaceMargin: int := 5; //non-reserved car park considered full when 5 spaces left
    var isWeekend: bool; //will determine if it is a weekend day or not as car park behaves different on weekend
    constructor() //constructor sets car park up for a new day
    ensures urArea == {} //ensuring that 
    ensures rArea == {}
    ensures subs == {}
    ensures capacity > 0;
    ensures rCapacity > 0;
    ensures isWeekend == false
    {
        //capacity := 20;
        rArea := {};
        urArea := {};
        isWeekend := false;
        subs := {};
    }

    predicate Valid()
    reads this
    {
        (|urArea| <= capacity - fullSpaceMargin) && (|rArea| <= capacity)
    }

    method EnterCarPark(carId : int)
    requires |urArea| < capacity - fullSpaceMargin; //- minSpaces;
    modifies this
    ensures urArea == old(urArea) + {carId}
    ensures rArea == old(rArea)
    ensures subs == old(subs)
    ensures |urArea| > 0
    ensures isWeekend == old(isWeekend)
    {
        //if the amount of cars is less than capacity then insert the car
        urArea := urArea + {carId};
    }

    method LeaveCarPark(carId : int)
    requires |urArea| > 0 || |rArea| > 0
    requires carId in urArea || carId in rArea
    modifies `urArea, `rArea
    ensures urArea == old(urArea) - {carId}
    ensures rArea == old(rArea) - {carId}
    ensures subs == old(subs)
    {
       // if(carId in urArea){
            urArea := urArea - {carId};
        //}else if(carId in rArea){
            rArea := rArea - {carId};
        //}
    }

    method CheckAvailability()
    modifies this
    ensures urArea == old(urArea)
    ensures rArea == old(rArea)
    ensures isWeekend == old(isWeekend)
    ensures subs == old(subs)
    {
        print "Current Non-reserved Availability: ";
        if(isWeekend){
            print weekendCapacity - (|rArea| + |urArea|);
        }else{
            print capacity - |urArea|;
        }
        print "\n";
    }

    method EnterReserve(carId: int)
    /*requires u == unreserved - {a}
    requires reserved == reserved - {a}
    requires |reserved| < reservedSpaces
    requires a in subscriptions || reservedOpen == true
    requires valid()
    modifies this
    ensures valid()
    ensures unreserved == old(unreserved)
    ensures reserved == old(reserved) + {a}
    ensures subscriptions == old(subscriptions)*/
    //requires urArea == urArea - {carId}
    //requires rArea == rArea - {carId}
    requires carId !in urArea
    requires carId !in rArea
    requires |rArea| < rCapacity
    requires carId in subs || isWeekend == true
    modifies this
    ensures urArea == old(urArea)
    ensures rArea == old(rArea) + {carId}
    ensures subs == old(subs)
    ensures isWeekend == old(isWeekend)
    ensures |rArea| > 0
    {
        rArea := rArea + {carId};
    }

    method MakeSubscription(carId: int)
    requires carId !in subs
    modifies this
    ensures urArea == old(urArea)
    ensures rArea == old(rArea)
    ensures isWeekend == old(isWeekend)
    ensures subs == old(subs) + {carId}
    {
        subs := subs + {carId};
    }

    method OpenReservedArea()
    modifies this
    ensures isWeekend == true
    ensures urArea == old(urArea)
    ensures rArea == old(rArea)
    ensures subs == old(subs)
    {
        isWeekend := true;
    }

    method CloseCarPark()
    modifies this
    ensures rArea == {}
    ensures urArea == {};
    ensures isWeekend == false; 
    {
        urArea := {};
        rArea := {};
        isWeekend := false;
    }

    method PrintParkingPlan()
    modifies this
    ensures isWeekend == old(isWeekend)
    ensures urArea == old(urArea)
    ensures rArea == old(rArea)
    ensures subs == old(subs)
    {
        print "Subscriptions: ";
        print subs;
        print "\n";
        print "Non-reserved area: ";
        print urArea;
        print "\n";
        print "Reserved Area: ";
        print rArea;
        print "\n";
    }
    /*method LeaveCarPark()
    requires |urArea| > 0
    modifies `urArea
    ensures |urArea| == |old(urArea)| - 1
    {
        var leavingCarId : int; //need to make a local var as dafny assume clause only supports local var currently
        leavingCarId :| leavingCarId in urArea; // taken from lecture 17 finds arbitrary value in the set to remove
        urArea := urArea - {leavingCarId}; //remove the arbitrary value from the set
    }*/
}

method Main(){
    var cp := new CarPark();

    //Showing everything from start
    /*print "Subscriptions: ";
    print cp.subs;
    print "\n";
    print "Non-reserved area: ";
    print cp.urArea;
    print "\n";
    print "Reserved Area: ";
    print cp.rArea;
    print "\n";*/

    /* TESTING A WEEKDAY */
    print "\n\nWEEKDAY PARKING\n\n";

    cp.PrintParkingPlan();

    cp.CheckAvailability();
    cp.EnterCarPark(1);

    cp.MakeSubscription(8);
    cp.EnterReserve(8);
    
    //cp.CloseCarPark();

    /* WEEKDAY IS FINISHED */

    /* TESTING WEEKEND */
    cp := new CarPark();

    print "\n\nWEEKEND PARKING\n\n";

    cp.OpenReservedArea();
    cp.EnterCarPark(15);

    cp.EnterReserve(2);
    cp.EnterReserve(3);
    cp.EnterReserve(4);

    cp.PrintParkingPlan();
    cp.CheckAvailability();

    cp.LeaveCarPark(3);

    cp.PrintParkingPlan();
    cp.CheckAvailability();

    /* WEEKEND IS FINISHED */

    /*print cp.urArea;
    cp.EnterCarPark(1);
    cp.EnterCarPark(2);
    cp.EnterCarPark(3);
    print cp.urArea;

    print "Checking avail: ";
    cp.CheckAvailability();
    print "\n";

    cp.LeaveCarPark(1);
    cp.LeaveCarPark(2);
    cp.LeaveCarPark(3);
    
    print cp.urArea;

    cp.EnterCarPark(2);
    cp.EnterCarPark(3);

    print cp.urArea;

    print "Checking avail: ";
    cp.CheckAvailability();
    print "\n";

    cp.OpenReserved();
    cp.EnterReserve(1);

    cp.CheckAvailability();*/
}