package test;

import ai.ComputerPlayer;
import ai.NaiveAI;
import ai.SmartAI;
import game.Game;
import game.Marble;
import game.Player;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class SmartAiTest {

    Player player1;
    Player player2;
    Game game;
    NaiveAI ai;

    @BeforeEach
    public void setUp() {
        //test NAIVE vs SMART
        ai = new NaiveAI();
        player1 = new ComputerPlayer(Marble.WHITE, ai);
        player2 = new SmartAI(Marble.BLACK);
        game = new Game(player1, player2);
        game.getBoard().clearBoard();
    }

    @Test
    public void testNaiveVsSmart() {
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
        assertTrue(game.getBoard().gameOver());
    }

    @Test
    public void testSmartVsNaive() {
        player1 = new SmartAI(Marble.WHITE);
        player2 = new ComputerPlayer(Marble.BLACK, ai);
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
        assertTrue(game.getBoard().gameOver());
    }

    @Test
    public void testSmartVsSmart() {
        player1 = new SmartAI(Marble.WHITE);
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
        assertTrue(game.getBoard().gameOver());
    }

    @Test
    public void testBoardScoreEvaluation() {

    }

    @Test
    public void testTimeForSingleMoveMadeByAI() {
        double startTime = System.currentTimeMillis();
        player2.determineMove(game.getBoard());
        player2.determineRotation(game.getBoard());
        double endTime = System.currentTimeMillis();
        double totalTimeSeconds = (endTime - startTime) / 1000;
        System.out.println("It took the smart player " + totalTimeSeconds +
                " seconds to determine it's first move.");
    }

    //Tests for the board score evaluation:
    @Test
    public void testHorizontalScoringOfBoard() {
        //Five marbles in a row: 10 points
        for (int i = 0; i < 5; i++) {
            game.getBoard().setField(i, Marble.WHITE);
        }
        assertEquals(10, game.getBoard().evaluateScore(Marble.WHITE));
        assertEquals(0, game.getBoard().evaluateScore(Marble.BLACK));
        game.getBoard().clearBoard();

        for (int i = 1; i < 6; i++) {
            game.getBoard().setField(i, Marble.BLACK);
        }
        assertEquals(10, game.getBoard().evaluateScore(Marble.BLACK));
        assertEquals(0, game.getBoard().evaluateScore(Marble.WHITE));
        game.getBoard().clearBoard();

        //Four marbles in a row: 6 points
        for (int i = 6; i < 10; i++) {
            game.getBoard().setField(i, Marble.WHITE);
        }
        assertEquals(6, game.getBoard().evaluateScore(Marble.WHITE));
        assertEquals(0, game.getBoard().evaluateScore(Marble.BLACK));
        game.getBoard().clearBoard();

        //Tree marbles in a row: 3 points
        for (int i = 13; i < 16; i++) {
            game.getBoard().setField(i, Marble.BLACK);
        }
        assertEquals(3, game.getBoard().evaluateScore(Marble.BLACK));
        assertEquals(0, game.getBoard().evaluateScore(Marble.WHITE));
        game.getBoard().clearBoard();

        //Two marbles in a row: 1 point
        game.getBoard().setField(27, Marble.BLACK);
        game.getBoard().setField(28, Marble.BLACK);
        assertEquals(1, game.getBoard().evaluateScore(Marble.BLACK));
        assertEquals(0, game.getBoard().evaluateScore(Marble.WHITE));
        game.getBoard().clearBoard();
    }


    @Test
    public void testUpwardDiagonalScoringOfBoard() {
        //Five marbles in a row: 10 points
        for (int row = 0; row < 5; row++) {
            game.getBoard().setField(5 - row, row, Marble.WHITE);
        }
        System.out.println("Board \n" + game.getBoard().toString());
        assertEquals(10, game.getBoard().evaluateScore(Marble.WHITE));
        assertEquals(0, game.getBoard().evaluateScore(Marble.BLACK));
        game.getBoard().clearBoard();

        for (int i = 1; i < 6; i++) {
            game.getBoard().setField(5 - i, i, Marble.BLACK);
        }
        System.out.println("Board \n" + game.getBoard().toString());
        assertEquals(10, game.getBoard().evaluateScore(Marble.BLACK));
        assertEquals(0, game.getBoard().evaluateScore(Marble.WHITE));
        game.getBoard().clearBoard();
    }

    @Test
    public void testBoardScoreForDiagonalWins() {
        game.getBoard().setField(7, Marble.WHITE);
        game.getBoard().setField(14, Marble.WHITE);
        game.getBoard().setField(21, Marble.WHITE);
        game.getBoard().setField(28, Marble.WHITE);
        game.getBoard().setField(35, Marble.WHITE);
        assertEquals(10, game.getBoard().evaluateScore(Marble.WHITE));
        game.getBoard().clearBoard();
    }




}