package ai;

import game.Board;
import game.Marble;

/**
 * Interface for our the AI implementations of the Pentago Project.
 */
public interface AI {
    /**
     *
     * @return the name of the AI implementation.
     */
    String getName();

    /**
     * @return the next legal move, given the board and player's marble.
     * @param marble the marble with which the Ai plays.
     * @param board the board on which the AI plays.
     */
    int determineMove(Board board, Marble marble);

    /**
     *
     * @return the next legal rotation, given the board.
     * @param board the board on which to determine a rotation.
     */
    int determineAiRotation(Board board);
}
