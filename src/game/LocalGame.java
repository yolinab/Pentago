package game;


import ai.ComputerPlayer;
import ai.NaiveAI;
import ai.SmartAIWithHints;

import java.util.Scanner;

/**
 * Class created for playing the game locally. Used to test the game logic / AI.
 */
public class LocalGame {
    private static String[] array;

    public static void main(String[] args)  {
        Scanner sc = new Scanner(System.in);
        System.out.println("Please input 2 names. (for AI's use \"-easy\" or \"-smart\"");
        Player player1 = null;
        Player player2 = null;
        while (array == null || array.length != 2) {
            System.err.println("The given argument input is invalid." +
                    " Please try again using name1 and name2");
            String input = sc.nextLine();
            array = input.split("\\s+");
        }
        //Since this class is mainly used for testing, we did not over-complicate its functionality.
        //Therefore, it might be a bit janky :(

        if (array[0].equals("-easy")) {
            if (!array[1].equals("-easy")) {
                player1 = new ComputerPlayer(Marble.WHITE, new NaiveAI());  //easy VS human
                player2 = new HumanPlayer(array[1], Marble.BLACK);
            }
            if (array[1].equals("-easy")) {
                player1 = new ComputerPlayer(Marble.WHITE, new NaiveAI());  //easy VS easy
                player2 = new ComputerPlayer(Marble.BLACK, new NaiveAI());
            }
            if (array[1].equals("-smart")) {
                player1 = new ComputerPlayer(Marble.WHITE, new NaiveAI());  //easy VS smart
                player2 = new SmartAIWithHints(Marble.BLACK);
            }
        } else if (array[0].equals("-smart")) {
            if (!array[1].equals("-easy")) {
                player1 = new SmartAIWithHints(Marble.WHITE);                       //smart VS human
                player2 = new HumanPlayer(array[1], Marble.BLACK);
            }
            if (array[1].equals("-easy")) {
                player1 = new SmartAIWithHints(Marble.WHITE);                        //smart VS easy
                player2 = new ComputerPlayer(Marble.BLACK, new NaiveAI());
            }
            if (array[1].equals("-smart")) {
                player1 = new SmartAIWithHints(Marble.WHITE);                       //smart VS smart
                player2 = new SmartAIWithHints(Marble.BLACK);
            }
        } else {
            if (!array[1].equals("-easy")) {
                player1 = new HumanPlayer(array[0], Marble.WHITE);            //human VS human
                player2 = new HumanPlayer(array[1], Marble.BLACK);
            }
            if (array[1].equals("-easy")) {
                player1 = new HumanPlayer(array[0], Marble.WHITE);            //human VS easy
                player2 = new ComputerPlayer(Marble.BLACK, new NaiveAI());
            }
            if (array[1].equals("-smart")) {
                player1 = new HumanPlayer(array[0], Marble.WHITE);            //human VS smart
                player2 = new SmartAIWithHints(Marble.BLACK);
            }
        }
        Game game = new Game(player1, player2);
        game.start();
    }
}
