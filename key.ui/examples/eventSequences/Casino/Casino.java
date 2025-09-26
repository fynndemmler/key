//import java.util.UUID;
import java.util.List;
import java.util.*;

enum Coin {
    HEADS,
    TAILS
}

enum State {
    IDLE,
    GAME_AVAILABLE,
    BET_PLACED
}

enum Methods {
    TRANSFER,
    REMOVE_FROM_POT,
    CREATE_GAME,
    PLACE_BET,
    DECIDE_BET
}

class Address {
    int id;
    int balance;

    /*@ normal_behavior
      @ requires id > 0 & balance > 0;
      @ ensures this.id == id & this.balance == balance;
     */
    public Address(int id, int balance) {
        this.id = id;
        this.balance = balance;
    }
}

/*
    Note that a falsey return value for any method in this class reflects aborted execution.
 */
class Casino {
    public Address operator;
    public Address player;
    public Coin guess;
    public int pot;
    public int hashedNumber;
    public int bet;
    private State state;

    // invariant operator != null && player != null && guess != null && state != null && State.BET_PLACED != null && state.GAME_AVAILABLE != null && state.IDLE != null && Coin.HEADS != null && Coin.TAILS != null;

    /*@ normal_behavior
      @ requires operator != null && player != null;
      @ ensures this.operator == operator && this.player == player && this.guess == Coin.HEADS && this.state == State.IDLE && this.pot == 0 && this.bet == 0 && this.hashedNumber == -1;
      @*/
    public void setupNewGame(Address operator, Address player) {
        this.operator = operator;
        this.player = player;
        this.guess = Coin.HEADS;
        state = State.IDLE;
        pot = 0;
        bet = 0;
        hashedNumber = -1;
    }

    // ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_removeFromPot_Address_int, TRUE))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_placeBet_Address_int_Coin, TRUE))\then(TRUE)\else(FALSE))))*); // Works
    // ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_placeBet_Address_int_Coin, TRUE))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_removeFromPot_Address_int, TRUE))\then(TRUE)\else(FALSE))))*); // Works
    /*@ normal_behavior
      @ requires operator != null && player != null && money > 0 && player != operator;
      @ ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_placeBet_Address_int_Coin, TRUE))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_removeFromPot_Address_int, TRUE))\then(TRUE)\else(FALSE))))*); // Works
      @*/
    public void allNonReoccuringMethodCallSequencesGame(Address operator, Address player, int money, Coin guess) {
       setupNewGame(operator, player);
       // Every single method call sequence should at least occur once (n * fac(n))
       //int[] methods = new int[]{Methods.TRANSFER, Methods.REMOVE_FROM_POT, Methods.CREATE_GAME, Methods.PLACE_BET, Methods.DECIDE_BET};
       //var method_sequences = permute(methods);
       //Methods[] method_sequences = new Methods[]{Methods.TRANSFER, Methods.CREATE_GAME, Methods.PLACE_BET, Methods.REMOVE_FROM_POT, Methods.DECIDE_BET};
       //int c = 0;
       placeBet(player, money, guess);
       removeFromPot(operator, money);
       //for (List<Integer> method_sequence : method_sequences) {
        /*
       for (Methods method : method_sequences) {
           if (method == Methods.TRANSFER) {
               casino.transfer(operator, 10);
           } else if (method == Methods.REMOVE_FROM_POT) {
               casino.removeFromPot(operator, 5);
           } else if (method == Methods.CREATE_GAME) {
               casino.createGame(operator, 1337);
           } else if (method == Methods.PLACE_BET) {
               Coin guess = c % 2 == 0 ? Coin.HEADS : Coin.TAILS;
               casino.placeBet(player, 10, guess);
           } else if (method == Methods.DECIDE_BET) {
               casino.decideBet(operator, 1337);
           }
           c = c + 1;
       }*/
       //}
    }

    /*
       Transfer money from an address. The money is just added to the pot and this abstract method
       simply reflects the transfer call from the original Casino contract. It has no effect on
       verification.
     */
    /*@ normal_behavior
      @ requires caller != null && amount > 0;
      @ ensures \result == true && caller.balance == \old(caller.balance) - amount;
      @*/
    public boolean transfer(Address caller, int amount) {
        caller.balance = caller.balance - amount;
        return true;
    }

    // Remove money from pot
    /*@ normal_behavior
      @ requires caller != null & amount > 0;
      @ ensures \result == false ==> state == State.BET_PLACED || caller != operator;
      @ ensures \result == true ==> transfer(caller, amount) && pot == \old(pot) - amount;
      @*/
    public boolean removeFromPot(Address caller, int amount) {
        // no active bet ongoing:
        if (this.state == State.BET_PLACED || caller != operator) {
           return false;
        }
        transfer(caller, amount);
        pot = pot - amount;
        return true;
    }

    // Operator opens a bet.
    /*@ normal_behavior
      @ requires caller != null && hashedNumber > 0;
      @ ensures \result == false ==> state != State.IDLE || caller != operator;
      @ ensures \result == true ==> this.hashedNumber == hashedNumber && state == State.GAME_AVAILABLE;
      @*/
    public boolean createGame(Address caller, int hashedNumber) {
        if (state != State.IDLE || caller != operator) {
            return false;
        }
        this.hashedNumber = hashedNumber;
        state = State.GAME_AVAILABLE;
        return true;
    }

    // Player places a bet
    /*@ normal_behavior
      @ requires caller != null && value > 0 && callerGuess != null;
      @ ensures \result == false ==> this.state != State.GAME_AVAILABLE || caller == this.operator || value > this.pot;
      @ ensures \result == true ==> state == State.BET_PLACED && player == caller && bet == value && this.guess == callerGuess;
     */
    public boolean placeBet(Address caller, int value, Coin callerGuess) {
        if (this.state != State.GAME_AVAILABLE || caller == this.operator || value > this.pot) {
            return false;
        }
        state = State.BET_PLACED;
        player = caller;
        bet = value;
        this.guess = callerGuess;
        return true;
    }

    // Operator resolves a bet
    /*@ normal_behavior
      @ requires caller != null && secretNumber > 0;
      @ ensures \result == false ==> state != State.BET_PLACED || caller != operator || hashedNumber != secretNumber;
      @ ensures \result == true ==> state == State.IDLE && ((secretNumber % 2 == 0 && guess == Coin.HEADS) ==> bet == 0 && pot == \old(pot) - \old(bet) && player.balance == transfer(\old(player), (int)(2*\old(bet)))) && (!(secretNumber % 2 == 0 && guess == Coin.HEADS) ==> pot == \old(pot) + \old(bet) && bet == 0);
      @*/
    public boolean decideBet(Address caller, int secretNumber) {
        if (state != State.BET_PLACED || caller != operator || hashedNumber != secretNumber) {
            return false;
        }
        Coin secret = (secretNumber % 2 == 0) ? Coin.HEADS : Coin.TAILS;

        if (secret == guess) {
            // player wins, gets back twice her bet
            pot = pot - bet;
            transfer(player, 2*bet);
            bet = 0;
        } else {
            // operator wins, bet trasnfered to pot
            pot = pot + bet;
            bet = 0;
        }
        state = State.IDLE;
        return true;
    }
}