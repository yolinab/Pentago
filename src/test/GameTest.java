package test;

import ai.ComputerPlayer;
import ai.NaiveAI;
//import ai.SmartAIWithHints;
import ai.SmartAIWithHints;
import game.Game;
import game.Marble;
import game.Player;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Test class for the local game logic.
 */
public class GameTest {

    Player player1;
    Player player2;
    Game game;
    ai.NaiveAI ai;


    @BeforeEach
    public void setUp() {
        ai = new NaiveAI();
        player1 = new ComputerPlayer(Marble.BLACK, ai);
        player2 = new SmartAIWithHints(Marble.WHITE);
        game = new Game(player1, player2);
    }

    @Test
    public void testGameLogicAndRules() {
        System.out.println("Starting board \n" + game.getBoard().toString());
        while (!game.getBoard().hasWinner()) {

            player1.makeMove(game.getBoard());
            player1.determineRotation(game.getBoard());
            game.getBoard().hasWinner();
            System.out.println("Player 1 has made a move + rotation : " + "\n" +
                    game.getBoard().toString());

            player2.makeMove(game.getBoard());
            player2.determineRotation(game.getBoard());
            game.getBoard().hasWinner();
            System.out.println("Player 2 has made a move + rotation : " + "\n" +
                    game.getBoard().toString());
        }
        //The functionality of all the methods that check the winner, including
        //hasWinner() have been tested in the BoardTest. Therefore, there is no need
        //to do the same thing in here. By just having it return true, it means that
        //the game ends.

        assertTrue(game.getBoard().gameOver());

    }
}
