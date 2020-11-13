chan feedbelt = [5] of {bool};


active proctype feedbelt_motor()
{
  do
  :: if
     :: full(feedbelt) -> progress:
       if
       :: feedbelt?[false] -> atomic { feedbelt ?_; printf("removed false\n")}
       :: else -> skip; printf("skipped\n")
       fi
     :: nfull(feedbelt) -> feedbelt ! false;
     fi
  od
}

active proctype adder()
{

 do
 :: true -> atomic { feedbelt!true;printf("added\n")}
 od
}

active proctype remover()
{

 do
 :: feedbelt?[true] -> atomic { feedbelt ?_; printf("removed true\n")}
 od
}

