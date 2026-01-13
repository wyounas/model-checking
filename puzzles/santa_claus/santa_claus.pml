/*
 * The Santa Claus Problem in Promela/SPIN
 * =======================================
 
Key points:
   - Santa does not marshal arrivals. Two "Room" processes do.
   - Each Room collects a fixed-size group, closes the entrance, and raises a request.
   - Santa waits for requests; reindeer requests have priority over elf requests.
   - After finishing a service action, Santa notifies the corresponding Room, which releases
     exactly that group and re-opens the entrance.
 

 To run this with Spin (version 6.5.2):

 $ spin -a santa_claus.pml
 $ gcc -O2 -o pan pan.c

 To verify a specific correctnes property:
 $ ./pan -N safety_delivery 

 */

#define NUM_REINDEER 9
#define NUM_ELVES 10
#define ELF_GROUP_SIZE 3

/* ===== CHANNELS ===== */

/* Arrivals are rendezvous: if the Room entrance is closed, the sender blocks. For Reindeer/Elf -> Room-reindeeer/Room-elf communication. */
chan r_arrive  = [0] of { bit };
chan e_arrive  = [0] of { bit };

/* Room releases exactly the waiting group via rendezvous sends. */
chan r_release = [0] of { bit };
chan e_release = [0] of { bit };

/* Santa -> Room "service complete" notification. */
chan r_done    = [0] of { bit };
chan e_done    = [0] of { bit };

byte reindeer_waiting = 0;
byte elf_waiting      = 0;

bit r_request = 0;  /* To signal to Santa that 9 reindeer are waiting */
bit e_request = 0;  /* To signal to Santa that 3 elves are waiting   */

bool delivering = false;
bool consulting = false;

active [NUM_REINDEER] proctype Reindeer()
{
    do
    :: r_arrive ! 1;     /* return from vacation and enter the room */
       r_release ? 1;    /* wait to be released after Santa's delivery */
    od
}

active [NUM_ELVES] proctype Elf()
{
    do
    :: e_arrive ! 1;     /* enter the elf room */
       e_release ? 1;    /* wait to be released after consultation */
    od
}

active proctype RoomReindeer()
{
    byte waiting = 0;
    byte i = 0;

    do
    /* Collect reindeer until the group is complete (entrance open iff waiting < 9) */
    :: (waiting < NUM_REINDEER) ->
        atomic {
            r_arrive ? 1;
            waiting++;
            reindeer_waiting = waiting;
            if
            :: (waiting == NUM_REINDEER) -> r_request = 1
            :: else -> skip
            fi
        }

    /* Group complete: wait for Santa, then release all 9 and reset */
    :: (waiting == NUM_REINDEER) ->
        atomic { r_done ? 1; i = 0; }

        do
        :: (i < NUM_REINDEER) ->
            atomic { r_release ! 1; i++; }
        :: else -> break
        od;

        atomic {
            waiting = 0;
            reindeer_waiting = 0;
        }
    od
}

active proctype RoomElf()
{
    byte waiting = 0;
    byte i = 0;

    do
    /* Collect elves until a group of 3 is complete (entrance open iff waiting < 3) */
    :: (waiting < ELF_GROUP_SIZE) ->
        atomic {
            e_arrive ? 1;
            waiting++;
            elf_waiting = waiting;
            if
            :: (waiting == ELF_GROUP_SIZE) -> e_request = 1
            :: else -> skip
            fi
        }

    /* Group complete: wait for Santa, then release all 3 and reset */
    :: (waiting == ELF_GROUP_SIZE) ->
        atomic { e_done ? 1; i = 0; }

        do
        :: (i < ELF_GROUP_SIZE) ->
            atomic { e_release ! 1; i++; }
        :: else -> break
        od;

        atomic {
            waiting = 0;
            elf_waiting = 0;
        }
    od
}

active proctype Santa()
{
    do
    /* Reindeer have priority when both requests are pending. */
    :: r_request ->
        atomic {
            delivering = true;
            r_request = 0;   /* claim the request */
        }

        /* Deliver toys (abstracted). */
        delivering = false;

        /* Notify the Room that delivery is complete; it can release the reindeer. */
        r_done ! 1;

    :: (!r_request && e_request) ->
        atomic {
            consulting = true;
            e_request = 0;   /* claim the request */
        }

        /* Consult. */
        consulting = false;

        /* Notify the Room; it can release the elves. */
        e_done ! 1;
    od
}

/* ===== Correctness Properties ===== */

/* Safety: Delivery only when all reindeer are present */
ltl safety_delivery { [] (delivering -> reindeer_waiting == NUM_REINDEER) }

/* Safety: Consultation only when enough elves are present */
ltl safety_consult  { [] (consulting -> elf_waiting == ELF_GROUP_SIZE) }

/* Mutual exclusion: Never both at once */
ltl mutex_santa     { [] !(delivering && consulting) }

/*
 * Progress: If a request is pending, eventually Santa performs some service.
 */
ltl live_progress { [] ( (r_request || e_request) -> <> (delivering || consulting) ) }
