class CarPark{
    var capacity : int; //total capacity car park can take
    var currentSize : int; //current size of the car park 
    var takenSpaces : set<int>; //the car park, will fill up with ids of car
    
    constructor(cap : int)
    requires cap > 0;
    ensures capacity == cap && currentSize == 0;
    ensures currentSize < capacity;
    ensures capacity > 0;
    {
        capacity := cap;
        currentSize := 0;
        takenSpaces := {};
    }

    method EnterCarPark(carId : int)
    modifies this
    {
        //if the amount of cars is less than capacity then insert the car
        if(currentSize < capacity){
            currentSize := currentSize + 1;
            takenSpaces := takenSpaces + {carId};
        }else{
            print "car park full";
        }
    }

    method LeaveCarPark() returns (leavingCarId : int)
    modifies this
    {
        //if the car park is empty print otherwise remove the car
        if(|takenSpaces| == 0){
            print "Car park empty";
        }else{
            leavingCarId :| leavingCarId in takenSpaces;
            takenSpaces := takenSpaces - {leavingCarId};
            currentSize := currentSize - 1;
        }
    }
}

method Main(){
    var cp := new CarPark(5);


    cp.EnterCarPark(1);
    cp.EnterCarPark(2);

    print cp.takenSpaces;


    var leftCar : int;
    leftCar := cp.LeaveCarPark();

    print cp.takenSpaces;
}