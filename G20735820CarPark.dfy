class {:autocontracts} CarPark{
    const capacity : int; //total capacity car park can take
    var urArea : set<int>; //the car park, will fill up with ids of car
    var rArea : set<int>;
    var arbitraryVal : int;
    constructor()
    ensures urArea == {}
    ensures rArea == {}
    ensures capacity > 0;
    {
        capacity := 20;
        rArea := {};
        urArea := {};
    }

    predicate Valid()
    reads this
    {
        (|urArea| <= capacity) //- minSpaces)
    }

    method EnterCarPark(carId : int)
    requires |urArea| < capacity; //- minSpaces;
    //requires Valid();
    modifies this
    //ensures Valid();
    ensures urArea == old(urArea) + {carId}
    {
        //if the amount of cars is less than capacity then insert the car
        urArea := urArea + {carId};
    }

    /*method LeaveCarPark(carId : int)
    modifies this
    {
        urArea := urArea - {carId};
    }*/

    method LeaveCarPark()
    requires |urArea| > 0
    modifies this
    ensures |urArea| == |old(urArea)| - 1
    {
        var leavingCarId : int; //need to make a local var as dafny assume clause only supports local var currently
        leavingCarId :| leavingCarId in urArea; // taken from lecture 17 finds arbitrary value in the set to remove
        urArea := urArea - {leavingCarId}; //remove the arbitrary value from the set
    }
}

method Main(){
    var cp := new CarPark();

    print cp.urArea;
    cp.EnterCarPark(1);
    cp.EnterCarPark(2);
    cp.EnterCarPark(3);
    print cp.urArea;

    cp.LeaveCarPark();
    cp.LeaveCarPark();
    cp.LeaveCarPark();
    
    print cp.urArea;


    cp.EnterCarPark(4);
    cp.EnterCarPark(5);
    cp.EnterCarPark(6);
    print cp.urArea;

    cp.LeaveCarPark();
    cp.LeaveCarPark();
    cp.LeaveCarPark();
    //cp.LeaveCarPark(2);
    print cp.urArea;
}