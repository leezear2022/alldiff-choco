package org.chocosolver.amtf.parser;

/**
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 26/01/11
 */
public class ParserException extends RuntimeException {
    public ParserException() {
    }

    public ParserException(String message) {
        super(message);
    }

    public ParserException(String message, Throwable cause) {
        super(message, cause);
    }

    public ParserException(Throwable cause) {
        super(cause);
    }
}
