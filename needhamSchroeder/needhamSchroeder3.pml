/**
	Needham-Schroeder message passing protocol. 
	|	msg1:	agentA -> agentB	(keyB, agentA, nonceA)
	|	msg2:	agentB -> agentA	(keyA, nonceA, nonceB)
	|	msg3:	agentA -> agentB	(keyB, nonceB, 0)

	Note that sending (keyB, agentA, nonceA) from agentA to agentB 
	over the network (chan)nel models agentA encrypting the message 
	"[agentA, nonceB]" with agentB's public key.
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
	nonceB,

	/*	Agent (I)ntruder */
	keyI, 
	agentI, 
	nonceI 
};


/**
	Declare a structured data type to model our encrypted messages.
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
	mtype pkey;			/* reciever's public key */
	mtype pnonce;		/* reciever's nonce	 */
	Crypt messageAB;	/* sent messages			 */
	Crypt data;			/* recieved messages	 */

	/* Initialization */
	partnerA = agentB;
	pkey	 = keyB;

	/* prepare (msg1) */
	messageAB.key = pkey;
	messageAB.content1 = agentA;
	messageAB.content2 = nonceA;

	/* send (msg1) */
	network ! msg1 (partnerA, messageAB);

	/* recv (msg2) : blocking */
	network ? (msg2, agentA, data);

	/* verify (msg2) : blocking	*/
	(data.key == keyA) && (data.content1 == nonceA);

	/* obtain (msg2) sender's nonce */
	pnonce = data.content2;

	/* prepare (msg3) */
	messageAB.key = pkey;
	messageAB.content1 = pnonce;
	messageAB.content2 = 0;

	/* send (msg3) */
	network ! msg3 (partnerA, messageAB);

	/* update status */
	statusA = ok;
}

/* Agent (B)ob */
active proctype Bob() {
		
	/* local variables */
	mtype pkey;			/* reciever's public key */
	mtype pnonce;		/* reciever's nonce	 */
	Crypt messageBA;	/* sent messages			 */
	Crypt data;			/* recieved messages	 */

	/* Initialization	*/
	partnerB = agentA;
	pkey	 = keyA;

	/* recv (msg1) : blocking */
	network ? (msg1, agentB, data)

	/* verify (msg1) : blocking */
	(data.key == keyB) && (data.content1 == agentA);

	/* obtain (msg1) sender's nonce */
	pnonce = data.content2;	

	/* prepare (msg2) */
	messageBA.key = pkey;
	messageBA.content1 = pnonce;
	messageBA.content2 = nonceB;

	/* send (msg2) */
	network ! msg2 (partnerB, messageBA);

	/* recv (msg3) : blocking */
	network ? (msg3, agentB, data);

	/* verify (msg3) : blocking */
	(data.key == keyB) && (data.content1 == nonceB);

	statusB = ok;
}

/* Agent (I)ntruder */
active proctype Intruder() {

	mtype msg, recpt;
	Crypt data, intercepted;

	do
	:: network ? (msg, _, data) -> 
	if /* perhaps store the message */
			
		::	intercepted.key		 = data.key;
			intercepted.content1 = data.content1;
			intercepted.content2 = data.content2;
			
		:: skip;
	fi;

	:: /* Replay or send a message */
	if /* choose message type */
		:: msg = msg1;
		:: msg = msg2;
		:: msg = msg3;
	fi;
		
	if /* choose a recepient */
		:: recpt = agentA;
		:: recpt = agentB;
	fi;
			 
	if /* replay intercepted message or assemble it */
		::	data.key		= intercepted.key;
			data.content1	= intercepted.content1;
			data.content2	= intercepted.content2;
		
		:: 
		if /* assemble content1 */
			:: data.content1 = agentA;
			:: data.content1 = agentB;
			:: data.content1 = agentI;
			:: data.content1 = nonceI;
		fi ;
		
		if /* assemble key */
			:: data.key = keyA;
			:: data.key = keyB;
			:: data.key = keyI;
		fi ;
		
		data.content2 = nonceI;
		
	fi ;

	network ! msg (recpt, data);
	od
}

ltl alwaysErr { [] ( (statusA == err) || (statusB == err) ) }

ltl eventuallyOk { <> ( (statusA == ok) && (statusB == ok) ) }