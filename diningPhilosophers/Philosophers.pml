// N defines the number of philosophers at the table. 
#define N 4

// CYCLES defines the number of updates that are run.
#define CYCLES 5

// Define a global variable which holds the total number of initialized philosophers. 
// We will use this as a way to engineer a blocking statement to prevent execution from 
// continuing. 
int initialized = 0;

// Since forks are a shared resource, we want to model them as a global variable. 
// The index of the array fork[N] represents the state of the fork, and the value 
// stored in the array represents the philosopher holding forks[N].
int forks[N];

// Note that each philosopher will have a unique ID.
proctype phil(int idN) {
	
	// We start by representing the fact that each philosopher starts with his own fork
	// We want to make sure all processes get iniitalized before entering the main execution 
	// loop, 
	forks[idN] = idN;

	// We will need to calculate the ids of the neighbors (to be used later). We need this step 
	// in order to establish a ring behaviour when updatig the state of forks. Note that this 
	// if statement will resolve deterministicly.
	int idL; 
	int idR;
	if 
	::  idN == 0; 
		idL = N - 1; 
		idR = idN + 1;

	::  idN == N-1; 
		idL = idN -1; 
		idR = 0; 

	::  else; 
		idL = idN - 1;
		idR = idN + 1;
	fi

	// This print statement verifies the initialization and verifies blocking behaviour
	printf("Initialized philosopher (%d) with neighbors (%d, %d)\n", idN, idL, idR)

	// Increment the total number of initializd philosophers.
	initialized++;
	
	// And check that all philosophers have been initialized prior to entering the executing the 
	// "do" loop.
	initialized == N;

	// Run two assertions to validate the closure property 
	assert( ( idL >= 0 && idL < N ) && ( idR >= 0 && idR < N ) );

	// As a secondary condition, we can can model check the initialization condition by the 
	// following assertion
	assert( forks[idN] == idN )

	// The logic for the entire update routine needs to go in an atomic block. The block 
	// should be designed such that there are no blocking processes. This represents a 
	// philosopher making a "complete decision" about how to update the global fork 
	// state before handing control back to the scheduler to another philosopher.
	int cycle = 0;
	do 
	:: cycle < CYCLES -> atomic {

		// ints to store the number of forks being held by this process philosopher(id) 
		// and the number of forks held by its neighbors (idL, idR)
		int Nforks = 0;
		int Lforks = 0; 
		int Rforks = 0;

		// array to store the number id of the forks being held by this process philosopher(id). 
		// note len(Nforks_data) = Nforks 
		int Nforks_data[2];		
		int Lforks_data[2];
		int Rforks_data[2];

		// This block loops through the fork[N] array and counts the number 
		// of forks held by this process.
		int i = 0;
		do
		:: i < N -> 
			if 
			:: forks[i] == idN; Nforks_data[Nforks] = i; Nforks++; i++;
			:: forks[i] == idL; Lforks_data[Lforks] = i; Lforks++; i++;
			:: forks[i] == idR; Rforks_data[Rforks] = i; Rforks++; i++;
			:: else; i++;
			fi 
		:: else -> break
		od

		// Assert that Nforks is 0,1,2. This ensures that the following if block is deterministic
		// and non-blocking
		assert( ( Nforks >= 0 && Nforks <= 2 ) && ( Lforks >= 0 && Lforks <= 2 ) && ( Rforks >= 0 && Rforks <= 2 ) ) 

		// This block takes care of the logic of exchanging forks. There are three possible 
		// cases Nforks IN {0, 1, 2}. Note that the print statements indicate the current state 
		// of the philosopher.
		if 	
			// Case of zero forks is the simplest. 
			:: 	Nforks == 0; 
				printf("Philosopher (%d) is thinking with NO forks \n", idN, Nforks);

			// Case of one fork			
			:: 	Nforks == 1; 
				printf("Philosopher (%d) is thinking with fork (%d) \n", idN, Nforks_data[0]);

				// First we deterministically discover who we can pass to, and then non-deterministicly
				// amogst the available options.
				if 
				// Case of both neighbors available
				:: ( Lforks != 2 ) && ( Rforks != 2 );
					if 
					:: forks[ Nforks_data[0] ] = idL;
					:: forks[ Nforks_data[0] ] = idR;
					:: skip;
					fi 

				// Left neighbor full (forced pass right or hold)
				:: ( Lforks == 2 ) && ( Rforks != 2 ); 
					if 
					:: forks[ Nforks_data[0] ] = idR;
					:: skip;
					fi

				// Right neighbor full (forced pass left or hold)
				:: ( Lforks != 2 ) && ( Rforks == 2 ); 
					if 
					:: forks[ Nforks_data[0] ] = idL
					:: skip; 
					fi
				// Case where both philosophers neighbors are full (needed for N >=5)
				:: ( Lforks == 2 ) && ( Rforks == 2 ); skip; 
				fi 

			:: 	Nforks == 2; 
				printf("Philosopher (%d) is eating with forks (%d) and (%d)\n", idN, Nforks_data[0], Nforks_data[1]);

				// In this case our philosopher is holding two forks, so we will non-deterministicly choose one 
				// of them to pass to the other philosophers.
				int _Fork; 
				if 
				:: _Fork = Nforks_data[0]	
				:: _Fork = Nforks_data[1]
				fi  

				// This branch is the same as the the Nforks == 1 case
				if 
				// Case of both neighbors available
				:: ( Lforks != 2 ) && ( Rforks != 2 );
					if 
					:: forks[ _Fork ] = idL;
					:: forks[ _Fork ] = idR;
					:: skip;
					fi 

				// Left neighbor full (forced pass right or hold)
				:: ( Lforks == 2 ) && ( Rforks != 2 ); 
					if 
					:: forks[ _Fork ] = idR;
					:: skip;
					fi

				// Right neighbor full (forced pass left or hold)
				:: ( Lforks != 2 ) && ( Rforks == 2 ); 
					if 
					:: forks[ _Fork ] = idL
					:: skip; 
					fi
				// Case where both philosophers neighbors are full (needed for N >=5)
				:: ( Lforks == 2 ) && ( Rforks == 2 ); skip; 
				fi
		fi 
	}; cycle++;
	:: else -> break
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
