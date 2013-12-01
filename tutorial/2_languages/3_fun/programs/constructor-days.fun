datatype day = Monday | Tuesday | Wednesday
             | Thursday | Friday | Saturday | Sunday

let day_after =
   fun Monday -> Tuesday
     | Tuesday -> Wednesday
     | Wednesday -> Thursday
     | Thursday -> Friday
     | Friday -> Saturday
     | Saturday -> Sunday
     | Sunday -> Monday
in letrec days_later =
   fun 0 day -> day
     | n day -> if n>0
                then days_later (n - 1) (day_after day)
                else days_later (n + 7) day
   in [days_later 2 Tuesday, days_later (-4) Wednesday, days_later 17 Monday]
