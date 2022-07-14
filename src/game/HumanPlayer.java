package game;


import java.util.Scanner;

/**
 * Class for maintaining a Human Player in Pentago.
 * @author Vlad Gosa and Yolina Yordanova
 */
public class HumanPlayer extends Player {

    //Constructor

    /**
     * Creates a new human player object.
     *
     * @param name   of the player
     * @param marble of his choice
     */
    /*@ requires name != null;
        requires marble == Marble.BLACK || marble == Marble.WHITE;
    @*/
    public HumanPlayer(String name, Marble marble) {
        super(name, marble);
    }

    //Commands

    /**
     *Determines the field for the next move.
     * @param board the current game board
     * @return the player's choice
     */
    /*@ requires board != null && board.isFull() == false;
        ensures board.isField(\result) && board.getField(\result) == Marble.EMPTY;
    @*/
    public int determineMove(Board board) {
        Scanner sc = new Scanner(System.in);
        String prompt = "> " + getName() + " (" + getMarble().toString() + ")"
                + ", what is your choice? ";

        System.out.println(prompt);
        int choice = sc.nextInt();

        boolean valid = board.isField(choice) && board.isEmptyField(choice);
        while (!valid) {
            System.out.println("ERROR: field " + choice
                    + " is no valid choice.");
            System.out.println(prompt);
            choice = sc.nextInt();
            valid = board.isField(choice) && board.isEmptyField(choice);
        }
        return choice;
    }

    /**
     * Determine the rotation after the marble has been placed
     * @param board the current game board
     */
    /*@ requires board!= null && board.isFull() == false;
    @*/
    public void determineRotation(Board board) {
        Scanner sc = new Scanner(System.in);
        String prompt = "> " + getName() + " (" + getMarble().toString() + ")"
                + ", what is your choice for the rotation? ";

        System.out.println(prompt);
        String choice = sc.nextLine();

        boolean valid = false;
        while (!valid) {
            switch (choice) {
                case "1+":
                    board.rotateFirstQuadrantClockwise();
                    valid = true;
                    break;
                case "1-":
                    board.rotateFirstQuadrantAntiClockwise();
                    valid = true;
                    break;
                case "2+":
                    board.rotateSecondQuadrantClockwise();
                    valid = true;
                    break;
                case "2-":
                    board.rotateSecondQuadrantAntiClockwise();
                    valid = true;
                    break;
                case "3+":
                    board.rotateThirdQuadrantClockwise();
                    valid = true;
                    break;
                case "3-":
                    board.rotateThirdQuadrantAntiClockwise();
                    valid = true;
                    break;
                case "4+":
                    board.rotateFourthQuadrantClockwise();
                    valid = true;
                    break;
                case "4-":
                    board.rotateFourthQuadrantAntiClockwise();
                    valid = true;
                    break;
                default:
                    choice = sc.nextLine();
            }
        }
    }
}
