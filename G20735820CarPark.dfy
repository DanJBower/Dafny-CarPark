class {:autocontracts} CarPark{
    const capacity : int := 10; //total capacity car park can take
    const rCapacity : int := 10;
    var urArea : set<int>; //the car park, will fill up with ids of car
    var rArea : set<int>;
    var subs: set<int>;
    const fullSpaceMargin: int := 5; //car park considered full when 5 spaces left
    var isWeekend: bool;
    constructor()
    ensures urArea == {}
    ensures rArea == {}
    ensures capacity > 0;
    ensures rCapacity > 0;
    ensures isWeekend == false
    {
        //capacity := 20;
        rArea := {};
        urArea := {};
        isWeekend := false;
    }

    predicate Valid()
    reads this
    {
        (|urArea| <= capacity) && (|rArea| <= capacity) //- minSpaces)
    }

    method EnterCarPark(carId : int)
    requires |urArea| < capacity - fullSpaceMargin; //- minSpaces;
    modifies `urArea
    ensures urArea == old(urArea) + {carId}
    {
        //if the amount of cars is less than capacity then insert the car
        urArea := urArea + {carId};
    }

    method LeaveCarPark(carId : int)
    requires |urArea| > 0
    requires carId in urArea || carId in rArea
    modifies `urArea, `rArea
    ensures urArea == old(urArea) - {carId}
    {
        if(carId in urArea){
            urArea := urArea - {carId};
        }else if(carId in rArea){
            rArea := rArea - {carId};
        }
    }

    method CheckAvailability()
    ensures urArea == old(urArea)
    ensures rArea == old(rArea)
    ensures isWeekend == old(isWeekend)
    ensures subs == old(subs)
    {
        if(isWeekend){
            print capacity - |rArea|;
        }else{
            print capacity - |urArea|;
        }
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

    print cp.urArea;
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

}