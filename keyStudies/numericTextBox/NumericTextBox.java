/**
 * This class represents a text box for numeric values.
 * Its content is represented as an array of single digits.
 *
 * Your task is to add JML contracts for each method in this class
 * that reflect the informal descriptions in the Javadoc comments.
 *
 * Also add JML invariants for the fields "cursorPosition" and "content" that make sure that
 *
 *  - the cursorPosition is always a valid value (see comment for cursorPosition).
 *  - the content before the cursor contains only single digits
 *  - the content after the cursor is EMPTY
 *
 * Furthermore, think about which methods are pure and use the appropriate annotation.
 *
 * Hint: If you use variables for array indices in an assignable-clause,
 *       their values are evaluated in the pre-state.
 */

/* A full implementation, where CLI interaction results in updating of a JFrame text box
 * which dynamically renders user input and reports errors. For this reason, the following 
 * packages are needed. 	
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
class NumericTextBoxData
{
	/* JML class invariants */
	/*
	 * (1) The cursorPosition is always a valid value (see comment for cursorPosition). 
	 *
	/*@ public invariant	  
	  @ 0 <= cursorPosition && cursorPosition <= content.length;
	  @*/

	/*
	 * (2) The content before the cursor contains only single digits
	 *
	/*@ public invariant	  
	  @ (\forall int i; 0 <= i && i < cursorPosition; 0 <= content[i] && content[i] <= 9);
	  @*/

	/*
	 * (3) The content after the cursor is EMPTY
	 *
	/*@ public invariant
	  @ cursorPosition < content.length && 
	  @ 		(\forall int i; i <= cursorPosition && cursorPosition < content.length; content[i] == -1);
	  @*/

	/**
	 * The current cursor position, i.e. the position after the previously entered digit.
	 * If this is 0, then the cursor is placed at the very beginning of the text box.
	 * Note that the number of possible cursor positions is greater by one than
	 * the length of the text box.
	 */
	private /*@ spec_public @*/ int cursorPosition;

	/**
	 * This array stores the contents of the text box. At every position
	 * before the cursor, there is a valid value (i.e. a single digit).
	 * Positions after the cursor must be EMPTY.
	 */
	private /*@nullable@*/ /*@ spec_public @*/ int[] content;

	/**
	 * Holds the current TextBoxRenderer. This can be null, which means that there
	 * is no renderer assigned.
	 */
	private /*@nullable@*/ /*@ spec_public @*/ TextBoxRenderer textBoxRenderer;

	/* EMPTY variable */
	private final int EMPTY = -1;;

	/* Class contructor */
	public NumericTextBoxData(int dataLength) {

		/* Initialize int data array */
		content = new int[dataLength];

		/* Re-initalize cursorPosition to zero */
		cursorPosition = 0;

		/* Fill array data with -1 */
		Arrays.fill(content, EMPTY);

		/* Initialize the renderer */
		textBoxRenderer	= new TextBoxRenderer();

		/* Force render the initial content */
		textBoxRenderer.contentChanged = true;
		textBoxRenderer.renderContent(content, cursorPosition);
	}

	/**
	 * Checks whether a given input is a single digit (i.e. between 0 and 9).
	 *
	 * @param input The input character.
	 * @return true if the input is a single digit, false otherwise.
	 *	
	 *
	/*@ public normal_behaviour
	  @ requires true;
	  @ ensures true;
	  @*/
	public boolean isSingleDigit(char input)
	{
		return Character.isDigit(input) ? true : false;
	}

	/**
	 * Enters a given input character into the text box and moves the cursor forward.
	 * If the input can be processed, the contentChanged flag of the current TextBoxRenderer (if any) is set.
	 * If an exception occurs, the TextBoxRenderer's showError flag is set instead.
	 *
	 * @param input the input character.
	 *
	 * @throws IllegalArgumentException if the input was not a single digit.
	 *
	 * @throws RuntimeException if the input was valid, but the cursor is at the end
	 *                          of the text box and no further input can be accepted.
	 *
	/*@ public normal_behaviour
	  @ requires content != null && textRenderer != null;
	  @ ensures true;
  	  @ assignable content[cursorPosition], cursorPosition, textBoxRenderer.contentChanged;
	  @	
	  @ also
	  @
	  @ public exceptional_behaviour
	  @ requires true
	  @ signals_only IllegalArgumentException;
	  @ signals (IllegalArgumentException) textBoxRenderer.showError == true;
	  @ assignable textBoxRenderer.showError;
	  @
	  @ also
	  @
	  @ public exceptional_behaviour
	  @ requires cursorPosition == content.length;
	  @ signals_only RuntimeException ;
	  @ signals (RuntimeException) textBoxRenderer.showError == true;
	  @ assignable textBoxRenderer.showError;
	  @*/
	public void enterCharacter(char input)
	{
		if ( !isSingleDigit(input) ) {
		
			textBoxRenderer.showError = true;
			throw new IllegalArgumentException("[ENTRY] is not a digit");
		}

		else if ( cursorPosition == content.length ) {
			textBoxRenderer.showError = true;
			throw new RuntimeException("[FULL] Cannot append data ");
		}

		else {

			/* Update data and cursor position */
			content[cursorPosition] = Integer.parseInt( Character.toString(input) );
			cursorPosition++;
	
			/* Tell the render that the content has changed */
			textBoxRenderer.contentChanged = true;
		}
	}

	/**
	 * Deletes the most recently entered character and moves the cursor back one position.
	 * Also sets the current TextBoxRenderer's contentChanged flag (if any).
	 *
	 * @throws RuntimeException if the cursor is at the very beginning. In this case
	 *                          the showError flag of the TextBoxRenderer is set
	 *                          before the exception is thrown.
	 *
	/*@ public normal_behaviour
	  @ requires content != null && textRenderer != null;
	  @ ensures content[cursorPosition] == -1;
	  @ ensures cursorPosition == \old(cursorPosition) - 1;
   	  @ assignable content[cursorPosition], cursorPosition, textBoxRenderer.contentChanged;
	  @
	  @ also
	  @
	  @ public exceptional_behaviour
	  @ requires cursorPosition == 0;
	  @ signals_only RuntimeException;
	  @ signals (RuntimeException) textBoxRenderer.showError == true;
	  @ assignable textBoxRenderer.showError;
	  @*/
	public void backspace()
	{
	
		if ( cursorPosition == 0 ) {

			textBoxRenderer.showError = true;
			throw new RuntimeException("[EMPTY] Invalid backspace");
		}
		else {
		
			content[cursorPosition - 1] = EMPTY;
			cursorPosition--;
			textBoxRenderer.contentChanged = true;

		}
	}

	/**
	 * Clears the text box and resets the cursor to the start.
	 * Also sets the contentChanged flag of the current TextBoxRenderer, if any.
	 */
	/*@ public normal_behaviour
	  @ requires content != null && textRenderer != null;;
	  @ ensures ( \forall int i; 0 <= i && i < content.length; content[i] == -1 );
	  @ ensures cursorPosition == 0;
	  @ assignable content[*], cursorPosition, textBoxRenderer.contentChanged;
	  @*/
	public void clear()
	{
		/* Re-initalize cursorPosition to zero */
		cursorPosition = 0;

		/* Fill array data with -1 */
		Arrays.fill(content, EMPTY);	
	
		/* Render the new textbox */
		textBoxRenderer.contentChanged = true;
	}

	/**
		Wrapper method for textBoxRender renderContent() method
	 */
	/*@ public normal_behaviour
	  @ requires content != null && textRenderer != null;;
	  @ ensures true;
	  @*/
	public void renderContent()
	{
		textBoxRenderer.renderContent(content, cursorPosition);
	}

	/**
		Wrapper method for textBoxRender renderError() method
	 */
	/*@ public normal_behaviour
	  @ requires textRenderer != null;
	  @ ensures true;
	  @*/
	public void renderError(String errorMessage)
	{
		textBoxRenderer.renderError(errorMessage);
	}	


	/**
		Wrapper method for textBoxRender renderContent() method
	*/
	/*@ public normal_behaviour
	  @ requires textRenderer != null;
	  @ ensures true;
	  @*/
	public void closeRenderer()
	{
		textBoxRenderer.closeRenderer();
	}	
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
