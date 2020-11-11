// Run the following with "spin -search -l progress.pml" to check for non-progress cycle
// and observe the output of spin, you may then run "spin -t -p progress.pml" to replay
// the trail produced

bool on;

active proctype flipflop()
{
  on = false;
  do
  :: on  -> on = false;
  :: !on -> progress: on = true;
  od
}
