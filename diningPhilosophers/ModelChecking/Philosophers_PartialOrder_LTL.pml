// Dining philosophers problem (adjacent variation)

// N defines the number of philosophers at the table. 
#define N 4

// Define a global variable which holds the total number of initialized philosophers. 
// This will be used to introduce a blocking statement which insures that all philosophers. 
// are initialized prior to proceeding with the interaction algorithm. 
int initialized = 0;

// Initialize array of ints which represents forks. The index of the array represents
// the position of the fork, and the value of the array indicates the occupation status
// of the fork.
//	1) A philosopher can only hold his fork of the fork to his immediate left. That is 
//	to say that forks[N] = {N, N-1}
// 	2) One fork cannot be held by more than one philosopher. This is taken care of by 
//	deisgn because we cannot have a situation where fork[N] takes more than one value
// 	indicating that more than one process is holding that fork.
// 	3) If a fork is not held, its status will be indicated as N = -1
int Forks[N]

// Inline methods to generate ring structure. We need to export these so we 
// can use them externally to check for deadlock.

// Macro to calculare the id of left neighbor
inline _idL(idN){

	if 
	::  idN == 0; 
		idL = N - 1;

	::  else; 
 		idL = idN - 1;
	fi	
}

// Macro to calculare the id of right neighbor
inline _idR(idN){

	if 	
	::  idN == N-1; 
		idR = 0; 
	
	::  else; 
		idR = idN + 1;
	fi
}

// Macro to calculate the deadlock state. This is a global variable which 
// will be updated once at the end of atomic block evaluation. Doing things 
// in this way will allow for a simple ltl formula.
int deadlock = 0

// Deadlock macro. Each process will check to see if a deadlock state has been reached.
inline update_deadlock_state(){

	// Assume a deadlock state
	int state = 1;

	// Check the forks array
	int i = 0;
	do
	:: i < N -> 

		// Need to calculate this for each check
		int iL;
		if 
		::  i == 0; 
			iL = N - 1;

		::  else; 
			iL = i - 1;
		fi	

		// Check the state
		state = ( ( Forks[i] == i || Forks[iL] == i )  && state ); i++;
	
	:: else -> break;
	od

	// Assign state to deadlock
	deadlock = state;
}

// Inline method to print the state of the Forks[N] array (for debug)
inline print_state(){

	printf("Forks = {\n" )
	
	int i = 0;
	
	do
	:: i < N -> 
		printf("%d, \n", Forks[i]); 
		i++;

	:: else -> 
		printf("}\n"); 
		printf("Deadlock = %d\n", deadlock); 
		break;
	od 
}

int eating = 0

// Note that each philosopher will have a unique ID.
proctype phil(int idN) {

	// Each philosopher must be aware of his left and right neighbors.
	// we will achieve this via the macros defined above. Since inlines 
	// are macros (not functions), they cannot return values to our process. 
	// We therefore need to declare two variables here to store our left 
	// and right neighbors.
	int idL;
	int idR; 

	// Call the macros to set idL and idR
	_idL(idN); 
	_idR(idN);

	// Initialize philosophers fork status to -1 (unoccupied)
	Forks[idN] = -1;

	// print statement verifies the initialization and blocking behaviour
	printf("Initialized philosopher (%d) with neighbors (%d, %d)\n", idN, idL, idR)

	// Increment the total number of initializd philosophers.
	initialized++;

	// And check that all philosophers have been initialized prior to entering the 
	// executing the main "do" loop.
	initialized == N;

	// The atomic block containing the logic of a philosopher updates the global state 
	// constitutes the critical section of the code. The atomicity prevents the scheduler 
	// from interleaving the state update mechanics of several processes.
	do 
	:: atomic {

		if
		// Occupancy 0 -> 0 transitions

		// If the philosophers fork is occuped by his right neighbor AND the philosophers
		// left neighbor occupies his fork, then he does nothing.
		:: (Forks[idN] == idR) && (Forks[idL] == idL); 
			printf("Philosopher (%d) is thinking with NO forks -> Cannot acquire fork\n", idN)


		// Occupancy 0 -> 1 transitions

		// In this case we try to guarantee that the philosopher acquires the lowest numbered resource first

		// If both forks are available, the philosopher acquires the lower numbered fork
		:: (Forks[idN] == -1) && (Forks[idL] == -1); 

			if 
			:: (idL < idN); Forks[idL] = idN 
			printf("Philosopher (%d) is thinking with NO forks -> Acquires fork (%d)\n", idN, idL)
			:: (idL > idN); Forks[idN] = idN
			printf("Philosopher (%d) is thinking with NO forks -> Acquires fork (%d)\n", idN, idN)
			fi

		// If the fork to the left of the philosopher is occupied and the philosophers fork 
		// is unoccupied.
		:: (Forks[idL] == idL) && (Forks[idN] == -1); 


			if 
			:: (idL < idN);
			printf("Philosopher (%d) is thinking with NO forks -> Cannot acquire fork\n", idN)
			:: (idL > idN); Forks[idN] = idN
			printf("Philosopher (%d) is thinking with NO forks -> Acquires fork (%d)\n", idN, idN)
			fi

	
		// If the fork to the left of philosopher is available and the philosophers fork 
		// is occupied by his right neighbor
		:: (Forks[idL] == -1) &&  (Forks[idN] == idR); 


			if 
			:: (idL < idN); Forks[idL] = idN
			printf("Philosopher (%d) is thinking with NO forks -> Acquires fork (%d)\n", idN, idL)
			:: (idL > idN);  
			printf("Philosopher (%d) is thinking with NO forks -> Cannot acquire fork\n", idN)
			fi 


		// Occupancy 1 -> 1 transitions

		// If the philosopher has his fork and his left neighbor has their fork, then the 
		// philosopher cannot acquire a fork.
		:: (Forks[idN] == idN) && (Forks[idL] == idL);

			printf("Philosopher (%d) is thinking with fork (%d) -> Cannot acquire fork\n", idN, idN)

		// If the philosopher has the fork of his left neighbor, and his fork is held by
		// his right neighbor, the philosopher cannot acquire a fork. 
		:: (Forks[idL] == idN) && (Forks[idN] == idR);

			printf("Philosopher (%d) is thinking with fork (%d) -> Cannot acquire fork\n", idN, idL)

		
		// Occupancy 1 -> 2 transitions	

		// If the philosopher occupies the fork on his left, and his fork is unoccupied, 
		// then he picks up his fork.
		:: (Forks[idL] == idN) && (Forks[idN] == -1) && (idL < idN);
			Forks[idN] = idN; 
			printf("Philosopher (%d) is thinking with fork (%d) -> Acquires fork (%d)\n", idN, idL, idN)	

		:: (Forks[idL] == -1) && (Forks[idN] == idN) && (idL > idN);
			Forks[idL] = idN; 
			printf("Philosopher (%d) is thinking with fork (%d) -> Acquires fork (%d)\n", idN, idL, idN)	


		// Occupancy 2 -> 0 transitions

		// If both the philosopher occupies his fork and the fork on his immediate left
		// then the philosopher is eating, and the forks are placed on the table.
		:: (Forks[idN] == idN) && (Forks[idL] == idN);

			label:
			Forks[idN] = -1;
			Forks[idL] = -1;
			printf("Philosopher (%d) is eating with forks (%d, %d) -> Releases Forks (%d, %d)\n", idN, idN, idL, idN, idL)

		fi 
	
		// Update deadlock state
		update_deadlock_state();

		// Debug
		print_state()
	}
	od
}
	

// Init process creates N philosopher processes with id = 0,1 ... N-1
// Note that init is also a process so the total number of processes is N+1
init {

	int i = 0;
	do
	:: i < N -> run phil(i); i++;
	:: else -> break
	od
}

// Model check that our model never deadlocks (pass)
ltl neverDeadlock { [] !deadlock }

// Model check that our model eventually deadlocks) should fail (pass)
ltl eventuallyDeadlock { <> deadlock }

// Model check that our model always initializes all processes (pass)
ltl eventuallyAlwaysInitialized{ <>[] (initialized == N) }

// Model check that process owns its fork infinitely often (fail)
ltl infinitelyOftenEating{ []<> (Forks[1] == 1 && Forks[0] == 1) }

// Model check that process owns its fork infinitely often (fail)
ltl infinitelyOftenAccess{ []<> (Forks[1] == -1 && Forks[0] == 1) }

