class NumericTextBoxData{

	/*@ public invariant	  
	  @ 0 <= cursorPosition && cursorPosition <= content.length;
	  @*/

	/*@ public invariant
	  @ (\forall int i; 0 <= i && i < cursorPosition; 0 <= content[i] && content[i] <= 9);
	  @*/

	/*@ public invariant
	  @ cursorPosition <= content.length && 
	  @ 		(\forall int i; cursorPosition <= i && i < content.length; content[i] == EMPTY || content[i] == 0);
	  @*/

	/* class invariants: the class constructor must be verified without class invariants.
	 * 					 all other class methods are verified including all invariants.
	 */
	private /*@spec_public@*/ int[] content;

	private /*@spec_public@*/ int cursorPosition = 0;

	private /*@spec_public@*/ TextBoxRenderer textBoxRenderer = new TextBoxRenderer();

	private final /*@ spec_public @*/ int EMPTY = -1;

	/*@ public normal_behaviour
	  @ requires size > 0; 
	  @ ensures (\forall int x; 0 <= x && x < content.length; content[x] == EMPTY );
	  @*/
	public NumericTextBoxData(int size){
		
		/* Create new content array */
		content = new int[size];

		/* Initialize (cursorPosition = 0) and (content[*] = EMPTY) */
		clear();
	}
	
	/*@ public normal_behaviour
	  @ requires content.length >= 0;
	  @ ensures cursorPosition == 0 && (\forall int x; 0 <= x && x < content.length; content[x] == EMPTY );
	  @ assignable cursorPosition, content[*], textBoxRenderer.contentChanged;
	  @*/
	public void clear(){
	
		cursorPosition = 0;

		int i = 0;

		/*@ loop_invariant
		  @ 0 <= i && i <= content.length && (\forall int x; 0 <= x && x < i; content[x] == EMPTY );
		  @ assignable content[*];
		  @ decreasing content.length - i;
		  @*/
		while (i < content.length){
			content[i] = EMPTY;
			i++; 
		}

		/* Update textBoxRenderer */
		textBoxRenderer.contentChanged = true;
	}

	/*@ public normal_behaviour
	  @ requires 0 <= cursorPosition && cursorPosition < content.length;
	  @ requires 48 <= input && input <= 57;
	  @ requires content[cursorPosition] == EMPTY;
	  @ ensures 0 <= content[\old(cursorPosition)] && content[\old(cursorPosition)] <= 9;
	  @ ensures cursorPosition == \old(cursorPosition) + 1;
	  @ assignable cursorPosition, content[cursorPosition], textBoxRenderer.contentChanged;
	  @
	  @ also
	  @
	  @ public exceptional_behaviour
	  @ requires input < 48 || input > 57;
	  @ signals_only IllegalArgumentException;
	  @ signals (IllegalArgumentException) cursorPosition == \old(cursorPosition);
	  @ assignable textBoxRenderer.showError;
	  @ also
	  @
	  @ public exceptional_behaviour
	  @ requires cursorPosition == content.length;
	  @ signals_only RuntimeException;
	  @ signals (RuntimeException) cursorPosition == \old(cursorPosition);
	  @ assignable textBoxRenderer.showError;
	  @*/
	public void enterCharacter(char input)
	{

		/* cast input as int (subtract ASCII '0') */ 
		int inputAsInt = (int)input - (int)'0';

		/* exceptional_behaviour: case of non-digit input */
		if (  inputAsInt < 0 || inputAsInt > 9 ) {

			textBoxRenderer.showError = true;
			throw new IllegalArgumentException("[ENTRY] is not a digit");
		}

		/* exceptional_behaviour: case of array full */
		if ( cursorPosition == content.length ) {

			textBoxRenderer.showError = true;
			throw new RuntimeException("[FULL] Cannot append data ");
		}

		/* normal_behaviour */
		content[cursorPosition] = inputAsInt;
		textBoxRenderer.contentChanged = true;
		cursorPosition++;
	}

	/*@ public normal_behaviour
	  @ requires cursorPosition > 0; 
	  @ ensures content[cursorPosition] == EMPTY;
	  @ ensures cursorPosition == \old(cursorPosition) - 1;
	  @ assignable cursorPosition, content[cursorPosition - 1], textBoxRenderer.contentChanged;
	  @
	  @ also 
	  @ 
	  @ public exceptional_behaviour
	  @ requires cursorPosition == 0;
	  @ signals_only RuntimeException;
	  @ signals (RuntimeException) cursorPosition == \old(cursorPosition);
  	  @ assignable textBoxRenderer.showError;
	  @*/
	public void backspace()
	{
		/* exceptional_behaviour: case of array full */

		if ( cursorPosition == 0 ) {

			textBoxRenderer.showError = true;
			throw new RuntimeException("[EMPTY] Invalid backspace");
		}
	
		/* normal_behaviour */			
		content[cursorPosition - 1] = EMPTY;
		textBoxRenderer.contentChanged = true;
		cursorPosition--;
	}
}

public class TextBoxRenderer
{
	public boolean contentChanged = false;

	public boolean showError = false;

	/*@ public normal_behaviour
	  @ requires true;
	  @ ensures true;
	  @*/
	public TextBoxRenderer() {	}
}