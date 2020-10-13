/**
	Needham-Schroeder message passing protocol. 
	|	msg1: 	agentA -> agentB	(keyB, agentA, nonceA)
	|	msg2: 	agentB -> agentA	(keyA, nonceA, nonceB)
	|	msg3: 	agentA -> agentB	(keyB, nonceB, 0)

	Note that sending (keyB, agentA, nonceA) from agentA to agentB 
	over the network (chan)nel models agentA encrypting the message 
	"[agentA, nonceB]" with agentB's public key.
*/

/**
	An mtype declaration allows for the introduction of symbolic names for constant values.
	The declaration

    	mtype = { ok, err, msg1, msg2, msg3}

	is functionally equivalent to the sequence of macro definitions:

	    #define	ok		5
	    #define err		4
	    #define	msg1	3
	    #define msg2	2
	    #define msg3	1
*/
mtype = {
	/* Status Codes */
	ok, 
	err, 

	/* Message Codes */
	msg1, 
	msg2, 
	msg3, 

	/*	Agent (A)lice */
	keyA,
	agentA, 
	nonceA,

	/*	Agent (B)ob */
	keyB, 
	agentB,
	nonceB
};


/**
	typedef - declare a structured data type to model our encrypted messages.
*/
typedef Crypt { 
	mtype key, 
	content1, 
	content2 
};


/**
	Model network between agents via a rendezvous channel. 
	Send and recieve operations are performed synchronously. 
*/
chan network = [0] of {mtype, mtype, Crypt};


/* global variables for verification*/
mtype partnerA; 
mtype partnerB;
mtype statusA = err;
mtype statusB = err;


/* Agent (A)lice */
active proctype Alice() {

	/* local variables */
	mtype pkey;			/* Bob's public key	*/
	mtype pnonce;		/* Bob's nonce 		*/
	Crypt messageAB; 	/* Alice's encrypted message to Bob		*/
	Crypt data;			/* Recieved encrypted message from Bob	*/

	/* Initialization */
	partnerA = agentB;
	pkey	 = keyB;

	/* Prepare the first message */
	messageAB.key = pkey;
	messageAB.content1 = agentA;
	messageAB.content2 = nonceA;

	/* Send the first message to the other party */
	network ! msg1 (partnerA, messageAB);

	/* 
		Wait for an answer. Observe that we are pattern-matching on the
		messages that start with msg2 and agentA, that is, we block until 
		we see a message with values msg2 and agentA as the first and second	
		components. The third component is copied to the variable data. 
	*/
	network ? (msg2, agentA, data);

	/* 
		We proceed only if the key field of the data matches keyA and the
		received nonce is the one that we have sent earlier; block otherwise.
	*/
	(data.key == keyA) && (data.content1 == nonceA);

	/* Obtain Bob's nonce */
	pnonce = data.content2;

	/* Prepare the last message */
	messageAB.key = pkey;
	messageAB.content1 = pnonce;
	messageAB.content2 = 0;	/* content2 is not used in the last message, just set it to 0 */


	/* Send the prepared messaage */
	network ! msg3 (partnerA, messageAB);


	/* and last - update the auxilary status variable */
	statusA = ok;
}

/* Agent (B)ob */
active proctype Bob() {
		
	/* local variables */
	mtype pkey;		/* Alice's public key	*/	
	mtype pnonce;   /* Alice's nonce  		*/
	Crypt messageBA	/* Bob's encrypted message for Alice	 */
	Crypt data;		/* received encrypted message from Alice */

	/* Initialization	*/
	partnerB = agentA;
	pkey	 = keyA;

	/*
		Wait for message from Alice. we block until we see a message with values 
		msg1 and agentB as the first and second	components. 
	*/
	network ? (msg1, agentB, data)

	(data.key == keyB) && (data.content1 == agentA);

	pnonce = data.content2;	

	/* Prepare the return message */
	messageBA.key = pkey;
	messageBA.content1 = pnonce;
	messageBA.content2 = nonceB;

	/**
		Construct a message to send back to Alice
	*/
	network ! msg2 (partnerB, messageBA);

	/*
		Recieve msg3
	*/
	network ? (msg3, agentB, data);

	(data.key == keyB) && (data.content1 == nonceB);

	statusB = ok;
}
ltl eventuallyOk { <> ( (statusA == ok) && (statusB == ok) ) }