import { forwardRef } from "react";
import Dialog from "@mui/material/Dialog";
import Typography from "@mui/material/Typography";
import CloseIcon from "@mui/icons-material/Close";
import LoadingButton from "@mui/lab/LoadingButton";
import Slide, { SlideProps } from "@mui/material/Slide";
import useMediaQuery from "@mui/material/useMediaQuery";
import { ThemeProvider, useTheme } from "@mui/material/styles";
import { Divider } from "@mui/material";
import _noop from "lodash/noop";

import { dialogTypography, muiTheme } from "../muiTheme";

import { checkIfTertiaryCtaIsAllowed } from "./helpers/muiDialog.general";

import {
  MODAL_TYPES,
  MODAL_CONFIGS,
  SIZE_TO_MAX_WIDTH,
  MODAL_SIZE_VS_CLASS_NAMES,
  MODAL_SIZES,
  TERTIARY_CTA_TYPES,
} from "./constants/muiDialog.types";
import {
  ConfirmationModalProps,
  InformationModalProps,
  InputModalProps,
} from "./constants/muiDialog.interfaces";

import "./muiDialog.scss";

type ModalProps =
  | InformationModalProps
  | ConfirmationModalProps
  | InputModalProps;

// Properly typed transition component
const TransitionUp = forwardRef<HTMLDivElement, SlideProps>(
  function Transition(props, ref) {
    return <Slide direction="up" ref={ref} {...props} />;
  }
);

const MuiDialog = (props: ModalProps) => {
  let parentTheme = useTheme();
  parentTheme = {
    ...parentTheme,
    typography: {
      ...parentTheme.typography,
      ...dialogTypography,
    },
  };

  const isMobile = useMediaQuery("(min-width:600px)");
  const subtype =
    props.type === MODAL_TYPES.INFORMATION
      ? (props as InformationModalProps).subtype
      : props.type === MODAL_TYPES.CONFIRMATION
        ? (props as ConfirmationModalProps).subtype
        : props.type === MODAL_TYPES.INPUT
          ? (props as InputModalProps).subtype
          : "default";

  const {
    wrapperClassName,
    open,
    type,
    size,
    title,
    subTitle,
    description,
    onClose,
    children,
    actions,
    showActions = true,
    showDivider = true,
    showCloseIcon = true,
    tertiaryCtaType = "default",
    ...rest
  } = props;
  const {
    primaryCtaTitle,
    secondaryCtaTitle,
    isPrimaryCtaLoading,
    isSecondaryCtaLoading,
    isPrimaryCtaDisabled = false,
    isSecondaryCtaDisabled = false,
    onPrimaryCtaClick = _noop,
    onSecondaryCtaClick = _noop,
    tertiaryCtaTitle,
    tertiaryCtaStartIcon,
    isTertiaryCtaLoading,
    isTertiaryCtaDisabled = false,
    onTertiaryCtaClick = _noop,
  } = actions || {};

  const config = MODAL_CONFIGS[type][subtype] || MODAL_CONFIGS[type].default;
  const defaultSize = config?.ALLOWED_SIZES[0] || MODAL_SIZES.SMALL;
  const selectedSize =
    size && config?.ALLOWED_SIZES?.includes(size) ? size : defaultSize;
  const showFooter = showActions && (primaryCtaTitle || secondaryCtaTitle);
  const showFooterDivider =
    showDivider &&
    (selectedSize === MODAL_SIZES.LARGE ||
      selectedSize === MODAL_SIZES.EXTRA_LARGE);
  const isTertiaryCtaAllowed = checkIfTertiaryCtaIsAllowed(
    type,
    subtype,
    selectedSize
  );
  const showTertiaryCta = isTertiaryCtaAllowed && tertiaryCtaTitle;

  const handleClose = () => {
    if (config?.DISMISSIBLE === "full") {
      onClose();
    }
  };

  const currentTheme = parentTheme || muiTheme;

  return (
    <ThemeProvider theme={currentTheme}>
      <Dialog
        TransitionComponent={isMobile ? TransitionUp : undefined}
        className={`vi-dialog ${MODAL_SIZE_VS_CLASS_NAMES[selectedSize]} ${wrapperClassName}`}
        open={open}
        onClose={handleClose}
        maxWidth={SIZE_TO_MAX_WIDTH[selectedSize]}
        fullWidth={true}
        {...rest}
      >
        <div className="p-24 h-fill">
          {title && (
            <div
              className={`vi-dialog-title ${MODAL_SIZE_VS_CLASS_NAMES[selectedSize]}`}
            >
              <div className="d-f ai-c jc-sb">
                <div className="d-f flex-dir-col gap-8">
                  <Typography variant="semiBoldLabelL">{title}</Typography>
                  {subTitle && (
                    <Typography variant="subtextM">{subTitle}</Typography>
                  )}
                </div>
                {showCloseIcon && (
                  <CloseIcon
                    fontSize="small"
                    className="close-icon"
                    aria-label="Close dialog"
                    onClick={onClose}
                  />
                )}
              </div>
              {description && (
                <Typography
                  component="div"
                  className="description"
                  // variant="subtextM"
                >
                  {description}
                </Typography>
              )}
            </div>
          )}
          {children}
          {showFooter && (
            <>
              {showFooterDivider && <Divider className="divider" />}
              {showTertiaryCta ? (
                <div className="vi-dialog-actions-wrapper">
                  <LoadingButton
                    className={`tertiary-cta ${
                      tertiaryCtaType === TERTIARY_CTA_TYPES.DESTRUCTIVE
                        ? "destructive"
                        : ""
                    }`}
                    variant="text"
                    onClick={onTertiaryCtaClick}
                    loading={!!isTertiaryCtaLoading}
                    disabled={
                      isTertiaryCtaDisabled !== undefined
                        ? isTertiaryCtaDisabled
                        : !!(isPrimaryCtaLoading || isSecondaryCtaLoading)
                    }
                    startIcon={tertiaryCtaStartIcon}
                  >
                    {tertiaryCtaTitle}
                  </LoadingButton>
                  <div
                    className={`vi-dialog-actions ${MODAL_SIZE_VS_CLASS_NAMES[selectedSize]}`}
                  >
                    {secondaryCtaTitle && (
                      <LoadingButton
                        className="vi-dialog-cta"
                        variant="outlined"
                        onClick={onSecondaryCtaClick}
                        disabled={
                          isSecondaryCtaDisabled !== undefined
                            ? isSecondaryCtaDisabled
                            : !!(isPrimaryCtaLoading || isTertiaryCtaLoading)
                        }
                        loading={!!isSecondaryCtaLoading}
                      >
                        {secondaryCtaTitle}
                      </LoadingButton>
                    )}
                    {primaryCtaTitle && (
                      <LoadingButton
                        className={`vi-dialog-cta ${subtype === "destructive" ? "destructive" : ""}`}
                        variant="contained"
                        onClick={onPrimaryCtaClick}
                        loading={!!isPrimaryCtaLoading}
                        disabled={
                          isPrimaryCtaDisabled !== undefined
                            ? isPrimaryCtaDisabled
                            : !!(isSecondaryCtaLoading || isTertiaryCtaLoading)
                        }
                      >
                        {primaryCtaTitle}
                      </LoadingButton>
                    )}
                  </div>
                </div>
              ) : (
                <div
                  className={`vi-dialog-actions without-tertiary ${MODAL_SIZE_VS_CLASS_NAMES[selectedSize]}`}
                >
                  {secondaryCtaTitle && (
                    <LoadingButton
                      className="vi-dialog-cta"
                      variant="outlined"
                      onClick={onSecondaryCtaClick}
                      disabled={
                        isSecondaryCtaDisabled !== undefined
                          ? isSecondaryCtaDisabled
                          : !!(isPrimaryCtaLoading || isTertiaryCtaLoading)
                      }
                      loading={!!isSecondaryCtaLoading}
                    >
                      {secondaryCtaTitle}
                    </LoadingButton>
                  )}
                  {primaryCtaTitle && (
                    <LoadingButton
                      className={`vi-dialog-cta ${subtype === "destructive" ? "destructive" : ""}`}
                      variant="contained"
                      onClick={onPrimaryCtaClick}
                      loading={!!isPrimaryCtaLoading}
                      disabled={
                        isPrimaryCtaDisabled !== undefined
                          ? isPrimaryCtaDisabled
                          : !!(isSecondaryCtaLoading || isTertiaryCtaLoading)
                      }
                    >
                      {primaryCtaTitle}
                    </LoadingButton>
                  )}
                </div>
              )}
            </>
          )}
        </div>
      </Dialog>
    </ThemeProvider>
  );
};

export default MuiDialog;
