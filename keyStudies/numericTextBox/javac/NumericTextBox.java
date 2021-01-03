/* A full implementation of NumericTextBox. CLI interaction results in updating of a JFrame text box
 * which renders user input and reports errors. For this reason, the following packages are needed. 	
 */
import java.util.*;  
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.SwingConstants;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.event.WindowEvent;

/* 
 * This class handles the data structure for the NumericTextBox and is the target of 
 * JML verification efforts regarding handling of user interaction.
 */
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

	/**
	 * This array stores the contents of the text box. At every position
	 * before the cursor, there is a valid value (i.e. a single digit).
	 * Positions after the cursor must be EMPTY.
	 */
	private /*@spec_public@*/ int[] content;

	/**
	 * The current cursor position, i.e. the position after the previously entered digit.
	 * If this is 0, then the cursor is placed at the very beginning of the text box.
	 * Note that the number of possible cursor positions is greater by one than
	 * the length of the text box.
	 */
	private /*@spec_public@*/ int cursorPosition = 0;

	/**
	 * Holds the current TextBoxRenderer. This can be null, which means that there
	 * is no renderer assigned.
	 */
	private /*@spec_public@*/ TextBoxRenderer textBoxRenderer = new TextBoxRenderer();

	private final /*@ spec_public @*/ int EMPTY = -1;

	/*@ public normal_behaviour
	  @ requires true;
	  @ ensures true;
	  @*/
	public NumericTextBoxData(int size){
		
		/* Create new content array */
		content = new int[size];

		/* Initialize (cursorPosition = 0) and (content[*] = EMPTY) */
		clear();

		/* Force render the initial content */
		textBoxRenderer.contentChanged = true;
		textBoxRenderer.renderContent(content, cursorPosition);
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

	/** Wrapper method for textBoxRender renderContent() method */
	public void renderContent()	{ textBoxRenderer.renderContent(content, cursorPosition); }

	/** Wrapper method for textBoxRender renderError() method  */
	public void renderError(String errorMessage) { textBoxRenderer.renderError(errorMessage); }	

	/**	Wrapper method for textBoxRender renderContent() method	*/
	public void closeRenderer() { textBoxRenderer.closeRenderer(); }
}

/**
 * This class implements a renderer that is responsible for displaying the
 * NumericTextBoxData data to the user.
 */
class TextBoxRenderer
{
	/**
	 * Whether the content was changed (so the rendered text box needs a refresh).
	 */
	public boolean contentChanged;

	/**
	 * Whether an exception occured (which should be represented in the rendered text box).
	 */
	public boolean showError;

	/*
	 * Public JFrame to display our data
	 */
	private JFrame frameTextBox; 
	private JLabel frameContent;

	/* Class constructor */ 
	public TextBoxRenderer() {
		
		contentChanged = false;

		showError = false;

		/* Initialize the GUI */
		frameTextBox = new JFrame("NumericTextBox");
		frameTextBox.setPreferredSize(new Dimension(400, 300));
		frameTextBox.pack();
    	frameTextBox.setLocationRelativeTo(null);
		frameContent = new JLabel("", SwingConstants.CENTER);

		/* Add the label to the text */
		frameTextBox.getContentPane().add(frameContent);
		frameTextBox.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		frameTextBox.setVisible(true);
	}

	/* Method to generate content string for current data */
	public String generateContentString(int[] content, int cursorPosition){

		String renderedData = new String("");

		/* Make some user content for empty textbox */
		if ( cursorPosition == 0 ) {
		
			return "[EMPTY] NumericTextBox";
		}

		/* Render NumericTextBoxData */
		else {
		
			int i;
			for (i = 0; i < cursorPosition; i++) { 

				// accessing each element of array 
				renderedData += Integer.toString(content[i]) + " "; 
			} 
			return ( cursorPosition == content.length ) ? renderedData + "[END]" : renderedData + "_";
		}
	}

	/* Method to update the label in the JFrame with content */
	public void renderContent(int[] content, int cursorPosition) {

		/* If content has changed, print it and set contentChanged to false */
		if (contentChanged) {
		
			frameContent.setForeground(Color.BLACK);
			frameContent.setText( generateContentString(content, cursorPosition) );
			contentChanged = false;
		}
	}

	/* Method to update the label in the JFrame with content */
	public void renderError(String errorMessage) {

		/* If showError has been set, print exception string */
		if (showError) {
			frameContent.setForeground(Color.RED);
			frameContent.setText( errorMessage );
			showError = false;
		}
	}
	
	/* Method to close the JFrame programmatically on program exit */
	public void closeRenderer() {
		frameTextBox.dispatchEvent(new WindowEvent(frameTextBox, WindowEvent.WINDOW_CLOSING));
	}
}

/** 
	This class contains the main() method. User interaction is implemented as a simple 
	command line interface (CLI). User data is handled by the NumericTextBoxData class, 
	and is rendered dynamically with the help of the TextBoxRenderer auxiliary class.
*/
public class NumericTextBox 
{

	public static NumericTextBoxData numericTextBoxData = new NumericTextBoxData(6);

	/* main method */
	public static void main(String[] args) {

		/* Simple numeric textbox cli */
		System.out.println("Enter [0-9], (b)ackspace, (c)lear or (q)uit");

		/* Get user input */
		Scanner scanner = new Scanner(System.in);

		/* Event loop */
    	while(true) {

    		try {
		
				char ch = scanner.next().charAt(0);

				/* Quit */
				if ( ch == 'q' ) { 
					numericTextBoxData.closeRenderer();
					break; 
				}
					
				/* Backspace */
				else if ( ch == 'b' ) { 
					numericTextBoxData.backspace();
				}

				/* Clear */
				else if ( ch == 'c' ) { 
					numericTextBoxData.clear();
				}

				/* Other charachters */
				else {
					numericTextBoxData.enterCharacter(ch);	
				}

				numericTextBoxData.renderContent();

    		}
    		catch (Exception e) {
				numericTextBoxData.renderError(e.getMessage());
    		}
		}	
	}
}
